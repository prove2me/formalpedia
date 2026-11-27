-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_4_14
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:32:46.703828+00:00
-- url     : https://prove2.me/submissions/bf6866f6-72b8-468a-b062-c49391d7a331

import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_GEPPGrowth_Main_lemma_4_13
import Theorems.Thm_GEPPGrowth_Main_lemma_4_10
import Theorems.Thm_GEPPGrowth_Main_lemma_4_8
import Theorems.Thm_GEPPGrowth_Main_lemma_4_2
import Theorems.Thm_MeasureTheory_lintegral_fintype_prod_eq_prod

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP414

open GEPPGrowth.Main

instance matBorel (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) ℝ) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → ℝ))

/-- The standard Gaussian on `Fin d → ℝ`. -/
abbrev gam (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => gaussianReal 0 1)

/-- The `n × n` standard Gaussian matrix law. -/
abbrev gM (n : ℕ) : Measure (Mat n) := GaussianMatrix.gaussianMatrix n n

instance gM_prob (n : ℕ) : IsProbabilityMeasure (gM n) :=
  GaussianMatrix.gaussianMatrix_isProbabilityMeasure n n

/-! ### Measurability of the Gaussian kernel `S ↦ normal S` -/

open scoped Matrix.Norms.L2Operator MatrixOrder in
lemma cont_sqrt (d : ℕ) : ContinuousOn (CFC.sqrt : Mat d → Mat d) {a | 0 ≤ a} :=
  CFC.continuousOn_sqrt

open scoped MatrixOrder in
lemma psd_closed (d : ℕ) : IsClosed {a : Mat d | 0 ≤ a} := by
  have : {a : Mat d | 0 ≤ a} = {a | ∀ i j : Fin d, a j i = a i j} ∩
      ⋂ x : Fin d → ℝ, {a | 0 ≤ x ⬝ᵥ (a *ᵥ x)} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Matrix.nonneg_iff_posSemidef,
      Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian.ext_iff, star_trivial]
  rw [this]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [dotProduct, Matrix.mulVec]; fun_prop

open scoped MatrixOrder in
lemma measurable_sqrt (d : ℕ) : Measurable (CFC.sqrt : Mat d → Mat d) := by
  classical
  have : (CFC.sqrt : Mat d → Mat d) =
      Set.piecewise {a : Mat d | 0 ≤ a} CFC.sqrt (fun _ => 0) := by
    funext a
    by_cases ha : 0 ≤ a
    · simp [Set.piecewise, ha]
    · simp only [Set.piecewise, Set.mem_setOf_eq, ha, if_false]
      exact CFC.sqrt_of_not_nonneg ha
  rw [this]
  exact ContinuousOn.measurable_piecewise (cont_sqrt d) continuousOn_const
    (psd_closed d).measurableSet

open scoped MatrixOrder in
lemma normal_eq_map (d : ℕ) (S : Mat d) :
    normal S = (gam d).map (fun y => CFC.sqrt S *ᵥ y) := by
  unfold normal multivariateGaussian
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext y i
  simp

open scoped MatrixOrder in
lemma normal_one (d : ℕ) : normal (1 : Mat d) = gam d := by
  rw [normal_eq_map, CFC.sqrt_one]
  simp [Matrix.one_mulVec, Measure.map_id']

lemma meas_entry {α : Type*} [MeasurableSpace α] {p q : ℕ} {f : α → Matrix (Fin p) (Fin q) ℝ}
    (hf : Measurable f) (a : Fin p) (b : Fin q) : Measurable (fun x => f x a b) :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hf)

lemma measurable_mulVec (d : ℕ) : Measurable (fun p : Mat d × Vec d => p.1 *ᵥ p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ =>
    (meas_entry measurable_fst i j).mul ((measurable_pi_apply j).comp measurable_snd)

open scoped MatrixOrder in
lemma measurable_normal (d : ℕ) : Measurable (fun S : Mat d => normal S) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hm : Measurable (fun p : Mat d × Vec d => CFC.sqrt p.1 *ᵥ p.2) :=
    (measurable_mulVec d).comp (((measurable_sqrt d).comp measurable_fst).prodMk measurable_snd)
  have : ∀ S : Mat d, normal S s =
      gam d (Prod.mk S ⁻¹' ((fun p : Mat d × Vec d => CFC.sqrt p.1 *ᵥ p.2) ⁻¹' s)) := by
    intro S
    have hmS : Measurable (fun y : Vec d => CFC.sqrt S *ᵥ y) :=
      (measurable_mulVec d).comp (measurable_const.prodMk measurable_id)
    rw [normal_eq_map, Measure.map_apply hmS hs]
    rfl
  simp_rw [this]
  exact measurable_measure_prodMk_left (hm hs)

lemma measurable_block (m : ℕ) : Measurable (fun S : CovState => block S m) :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

/-- Extension of a vector by zeros. -/
def ext (m : ℕ) (v : Vec m) : ℕ → ℝ := fun i => if h : i < m then v ⟨i, h⟩ else 0

lemma measurable_ext (m : ℕ) : Measurable (ext m) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i < m
  · simp only [ext, h, dif_pos]; exact measurable_pi_apply _
  · simp only [ext, h, dif_neg, not_false_eq_true]; exact measurable_const

/-! ### Measurability of the covariance update -/

lemma measurable_foldl {α : Type*} [MeasurableSpace α] {k : ℕ}
    (g : α → Fin k → Fin k → Fin k) (hg : ∀ j, Measurable (fun p : α × Fin k => g p.1 p.2 j))
    (l : List (Fin k)) :
    ∀ b : α → Fin k, Measurable b → Measurable (fun a => l.foldl (g a) (b a)) := by
  induction l with
  | nil => intro b hb; simpa using hb
  | cons j l ih => intro b hb; exact ih _ ((hg j).comp (measurable_id.prodMk hb))

lemma measurable_pivot (d : ℕ) : Measurable (fun y : Vec (d+1) => pivot y) := by
  unfold pivot
  refine measurable_foldl _ (fun j => ?_) _ _ measurable_const
  refine measurable_from_prod_countable_left fun b => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  simp only [Set.setOf_or, Set.setOf_and]
  exact (measurableSet_lt (by fun_prop) (by fun_prop)).union
    ((measurableSet_eq_fun (by fun_prop) (by fun_prop)).inter (MeasurableSet.const _))

lemma measurable_compressionAt (d : ℕ) (i : Fin (d+1)) :
    Measurable (fun y : Vec (d+1) => compressionAt y i) := by
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  simp only [compressionAt, eliminationAt, ratiosAt, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply]
  fun_prop

lemma measurable_updateAt (d : ℕ) (i : Fin (d+1)) :
    Measurable (fun p : Mat (d+1) × Vec (d+1) => updateAt p.1 p.2 i) := by
  have hC : Measurable (fun p : Mat (d+1) × Vec (d+1) => compressionAt p.2 i) :=
    (measurable_compressionAt d i).comp measurable_snd
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  simp only [updateAt, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.measurable_sum _ fun e _ => Measurable.mul
    (Finset.measurable_sum _ fun f _ => (meas_entry hC a f).mul (meas_entry measurable_fst f e))
    (meas_entry hC b e)

lemma measurable_update (d : ℕ) :
    Measurable (fun p : Mat (d+1) × Vec (d+1) => updateAt p.1 p.2 (pivot p.2)) := by
  have h : Measurable (fun q : (Mat (d+1) × Vec (d+1)) × Fin (d+1) => updateAt q.1.1 q.1.2 q.2) :=
    measurable_from_prod_countable_left fun i => measurable_updateAt d i
  have h2 : Measurable (fun p : Mat (d+1) × Vec (d+1) => (p, pivot p.2)) :=
    measurable_id.prodMk ((measurable_pivot d).comp measurable_snd)
  have := h.comp h2
  simp only [Function.comp_def] at this
  exact this

lemma measurable_embed (d : ℕ) : Measurable (fun M : Mat d => embed M) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  by_cases hi : i < d
  · by_cases hj : j < d
    · simp only [embed, hi, hj, dif_pos]; exact meas_entry measurable_id _ _
    · simp only [embed, hi, hj, dif_pos, dif_neg, not_false_eq_true]; exact measurable_const
  · simp only [embed, hi, dif_neg, not_false_eq_true]; exact measurable_const

lemma measurable_stateUpdate (m : ℕ) :
    Measurable (fun p : CovState × (ℕ → ℝ) => stateUpdate m p.1 p.2) := by
  cases m with
  | zero => exact measurable_fst
  | succ d =>
    have e : (fun p : CovState × (ℕ → ℝ) => stateUpdate (d+1) p.1 p.2) =
        fun p => embed (updateAt (block p.1 (d+1)) (fun j : Fin (d+1) => p.2 j.val)
          (pivot (fun j : Fin (d+1) => p.2 j.val))) := by
      funext p; simp only [stateUpdate, update]
    rw [e]
    have h1 : Measurable (fun p : CovState × (ℕ → ℝ) =>
        (block p.1 (d+1), (fun j : Fin (d+1) => p.2 j.val))) :=
      ((measurable_block (d+1)).comp measurable_fst).prodMk
        (measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_snd)
    have := (measurable_embed d).comp ((measurable_update d).comp h1)
    simp only [Function.comp_def] at this
    exact this

lemma covStep_eq (m : ℕ) (S : CovState) :
    covStep m S = (normal (block S m)).map (fun v => stateUpdate m S (ext m v)) := by
  cases m with
  | zero => simp [covStep, stateUpdate, Measure.map_const]
  | succ d =>
    simp only [covStep, stateUpdate]
    congr 2
    funext v
    congr 2
    funext j
    simp [ext, j.isLt]

/-! ### Generic measure-theory helpers -/

lemma bind_apply_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (κ : α → Measure β) {s : Set β} (hs : MeasurableSet s) :
    μ.bind κ s ≤ ∫⁻ a, κ a s ∂μ := by
  by_cases h : AEMeasurable κ μ
  · rw [Measure.bind_apply hs h]
  · simp [Measure.bind, Measure.map_of_not_aemeasurable h]

/-- A set whose outer measure and that of its complement add up to the total mass is
null-measurable (Carathéodory). -/
lemma nullMeasurableSet_of_add {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (S : Set α) (h : μ S + μ Sᶜ ≤ μ Set.univ) : NullMeasurableSet S μ := by
  set T := toMeasurable μ S
  have hST : S ⊆ T := subset_toMeasurable μ S
  have hT : MeasurableSet T := measurableSet_toMeasurable μ S
  have hμT : μ T = μ S := measure_toMeasurable S
  have h1 : μ (Sᶜ ∩ T) + μ (Sᶜ \ T) = μ Sᶜ := measure_inter_add_diff _ hT
  have h2 : Sᶜ \ T = Tᶜ := by
    ext x
    simp only [Set.mem_diff, Set.mem_compl_iff, and_iff_right_iff_imp]
    exact fun hx hS => hx (hST hS)
  have h3 : μ Tᶜ = μ Set.univ - μ T := measure_compl hT (measure_ne_top _ _)
  have h4 : μ Sᶜ ≤ μ Tᶜ := by
    rw [h3, hμT]
    exact ENNReal.le_sub_of_add_le_left (measure_ne_top _ _) h
  have h5 : μ (Sᶜ ∩ T) = 0 := by
    rw [h2] at h1
    have : μ (Sᶜ ∩ T) + μ Tᶜ ≤ 0 + μ Tᶜ := by rw [zero_add, h1]; exact h4
    exact le_antisymm (ENNReal.le_of_add_le_add_right (measure_ne_top _ _) this) bot_le
  refine hT.nullMeasurableSet.congr ?_
  refine (ae_eq_set.2 ⟨?_, ?_⟩)
  · rw [Set.diff_eq, Set.inter_comm]; exact h5
  · rw [Set.diff_eq_empty.2 hST]; exact measure_empty

/-! ### One step of the coupling -/

/-- If, conditionally on `F A`, the residual column `actualColumn A t` has the Gaussian law with
covariance `block (c (F A)) (n-t)`, then the covariance process at time `t+1` is dominated by the
law of `actualCov A (t+1)`, given the same at time `t`. -/
lemma step (n t : ℕ) {X : Type*} [MeasurableSpace X] (F : Mat n → X) (hF : Measurable F)
    (c : X → CovState) (hc : Measurable c) (hcF : ∀ A, c (F A) = actualCov A t)
    (hjoint : ∀ H B, MeasurableSet H → MeasurableSet B →
      gM n {A | F A ∈ H ∧ actualColumn A t ∈ B} =
        ∫⁻ A in {A | F A ∈ H}, normal (block (c (F A)) (n-t)) (ext (n-t) ⁻¹' B) ∂(gM n))
    (IH : ∀ E, MeasurableSet E → covLaw n t E ≤ gM n {A | actualCov A t ∈ E}) :
    ∀ E, MeasurableSet E → covLaw n (t+1) E ≤ gM n {A | actualCov A (t+1) ∈ E} := by
  intro E hE
  set m := n - t with hm
  have hκm : Measurable (fun x : X => (normal (block (c x) m)).map (ext m)) :=
    (Measure.measurable_map _ (measurable_ext m)).comp
      ((measurable_normal m).comp ((measurable_block m).comp hc))
  let κ : Kernel X (ℕ → ℝ) := ⟨fun x => (normal (block (c x) m)).map (ext m), hκm⟩
  have hκ : ∀ x B, MeasurableSet B → κ x B = normal (block (c x) m) (ext m ⁻¹' B) :=
    fun x B hB => Measure.map_apply (measurable_ext m) hB
  haveI : IsMarkovKernel κ :=
    ⟨fun x => Measure.isProbabilityMeasure_map (measurable_ext m).aemeasurable⟩
  set Y : Mat n → ℕ → ℝ := fun A => actualColumn A t
  -- the residual column is a.e.-measurable
  have hY : AEMeasurable Y (gM n) := by
    refine NullMeasurable.aemeasurable fun B hB => ?_
    refine nullMeasurableSet_of_add _ _ ?_
    have e1 := hjoint Set.univ B MeasurableSet.univ hB
    have e2 := hjoint Set.univ Bᶜ MeasurableSet.univ hB.compl
    simp only [Set.mem_univ, true_and, Set.setOf_true, Measure.restrict_univ] at e1 e2
    have hs : (Y ⁻¹' B)ᶜ = {A | actualColumn A t ∈ Bᶜ} := rfl
    have hmB : Measurable (fun A => normal (block (c (F A)) m) (ext m ⁻¹' B)) := by
      have : (fun A => normal (block (c (F A)) m) (ext m ⁻¹' B)) = (fun x => κ x B) ∘ F := by
        funext A; exact (hκ _ _ hB).symm
      rw [this]; exact (Kernel.measurable_coe κ hB).comp hF
    rw [hs, show Y ⁻¹' B = {A | actualColumn A t ∈ B} from rfl, e1, e2,
      ← lintegral_add_left hmB]
    simp only [Set.preimage_compl]
    have : ∀ A : Mat n, normal (block (c (F A)) m) (ext m ⁻¹' B) +
        normal (block (c (F A)) m) (ext m ⁻¹' B)ᶜ = 1 := by
      intro A
      rw [measure_add_measure_compl ((measurable_ext m) hB), measure_univ]
    simp_rw [this]
    simp
  have hFY : AEMeasurable (fun A => (F A, Y A)) (gM n) := hF.aemeasurable.prodMk hY
  -- the joint law of `(F A, Y A)`
  have hjl : (gM n).map (fun A => (F A, Y A)) = ((gM n).map F) ⊗ₘ κ := by
    haveI : IsProbabilityMeasure ((gM n).map (fun A => (F A, Y A))) :=
      Measure.isProbabilityMeasure_map hFY
    haveI : IsProbabilityMeasure ((gM n).map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨H, hH, B, hB, rfl⟩
      rw [Measure.map_apply_of_aemeasurable hFY (hH.prod hB), Measure.compProd_apply_prod hH (show MeasurableSet B from hB),
        setLIntegral_map hH (Kernel.measurable_coe κ hB) hF]
      have := hjoint H B hH hB
      simp_rw [hκ _ _ hB]
      exact this
    · simp [measure_univ]
  set G : Set (X × (ℕ → ℝ)) := {p | stateUpdate m (c p.1) p.2 ∈ E}
  have hG : MeasurableSet G :=
    (measurable_stateUpdate m).comp ((hc.comp measurable_fst).prodMk measurable_snd) hE
  have key : gM n {A | actualCov A (t+1) ∈ E} =
      ∫⁻ A, covStep m (actualCov A t) E ∂(gM n) := by
    have h1 : {A | actualCov A (t+1) ∈ E} = (fun A => (F A, Y A)) ⁻¹' G := by
      ext A
      simp only [G, Set.mem_setOf_eq, Set.mem_preimage, hcF]
      rfl
    rw [h1, ← Measure.map_apply_of_aemeasurable hFY hG, hjl, Measure.compProd_apply hG,
      lintegral_map (Kernel.measurable_kernel_prodMk_left hG) hF]
    refine lintegral_congr fun A => ?_
    have hmeas : Measurable (fun v => stateUpdate m (actualCov A t) (ext m v)) :=
      (measurable_stateUpdate m).comp (measurable_const.prodMk (measurable_ext m))
    rw [covStep_eq, Measure.map_apply hmeas hE, hκ _ _ (measurable_prodMk_left hG), ← hcF]
    rfl
  have hmeasC : Measurable (fun A : Mat n => actualCov A t) := by
    have : (fun A : Mat n => actualCov A t) = c ∘ F := by funext A; exact (hcF A).symm
    rw [this]; exact hc.comp hF
  have hle : covLaw n t ≤ (gM n).map (fun A => actualCov A t) :=
    Measure.le_iff.2 fun s hs => by rw [Measure.map_apply hmeasC hs]; exact IH s hs
  calc covLaw n (t+1) E = (covLaw n t).bind (covStep m) E := rfl
    _ ≤ ∫⁻ S, covStep m S E ∂(covLaw n t) := bind_apply_le _ _ hE
    _ ≤ ∫⁻ S, covStep m S E ∂((gM n).map (fun A => actualCov A t)) := lintegral_mono' hle le_rfl
    _ ≤ ∫⁻ A, covStep m (actualCov A t) E ∂(gM n) := lintegral_map_le _ _
    _ = _ := key.symm

/-! ### The coupling `covLaw n K ≤ law of actualCov A K` -/

lemma block_embed {d : ℕ} (M : Mat d) : block (embed M) d = M := by
  ext i j; simp [block, embed]

lemma gM_map_col (n : ℕ) (j : Fin n) : (gM n).map (fun A i => A i j) = gam n := by
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1))
    (f := fun (_ : Fin n) (x : Fin n → ℝ) => x j) (fun _ => (measurable_pi_apply j).aemeasurable)
  change (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0 1).map
    (fun A i => A i j) = gam n
  rw [h]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) j).map_eq

lemma columnsLaw_map_col {d : ℕ} (S : Mat d) (m : ℕ) (j : Fin m) :
    (columnsLaw S m).map (fun M i => M i j) = normal S := by
  unfold columnsLaw
  have hT : Measurable (fun z : Fin m → Vec d => (fun i j => z j i : Matrix (Fin d) (Fin m) ℝ)) := by
    change Measurable (fun z : Fin m → Vec d => fun i j => z j i)
    fun_prop
  have hC : Measurable (fun M : Matrix (Fin d) (Fin m) ℝ => fun i => M i j) :=
    measurable_pi_lambda _ fun i => meas_entry measurable_id i j
  rw [Measure.map_map hC hT]
  exact (measurePreserving_eval (fun _ : Fin m => normal S) j).map_eq

lemma actualColumn_eq {n : ℕ} (A : Mat n) (K : ℕ) (hK : K < n) :
    actualColumn A K = ext (n-K) (fun i => residual A K i ⟨0, by omega⟩) := by
  funext i
  by_cases hi : i < n - K
  · have hi' : i + K < n := by omega
    simp [actualColumn, ext, GEPPGrowth.Main.residual, hi, hi', hK]
  · have hi' : ¬ i + K < n := by omega
    simp [actualColumn, ext, hi, hi']

lemma coupling (n : ℕ) : ∀ K, K < n → ∀ E, MeasurableSet E →
    covLaw n K E ≤ gM n {A | actualCov A K ∈ E}
  | 0, _ => fun E hE => by
      show Measure.dirac (embed (1 : Mat n)) E ≤ gM n {A | embed (1 : Mat n) ∈ E}
      by_cases h : embed (1 : Mat n) ∈ E
      · simp [h]
      · rw [Measure.dirac_apply' _ hE]; simp [h]
  | K+1, hK => by
      have IH := coupling n K (by omega)
      rcases Nat.eq_zero_or_pos K with rfl | hpos
      · refine step n 0 (X := Unit) (fun _ => ()) measurable_const (fun _ => embed (1 : Mat n))
          measurable_const (fun A => rfl) ?_ IH
        intro H B hH hB
        show gM n {A | () ∈ H ∧ actualColumn A 0 ∈ B} =
          ∫⁻ A in {A : Mat n | () ∈ H}, normal (block (embed (1 : Mat n)) n) (ext n ⁻¹' B) ∂gM n
        by_cases h : () ∈ H
        · have hcol : ∀ A : Mat n, actualColumn A 0 = ext n (fun i => A i ⟨0, by omega⟩) := by
            intro A; rw [actualColumn_eq A 0 (by omega)]; rfl
          simp only [h, true_and, Set.setOf_true, Measure.restrict_univ, lintegral_const,
            measure_univ, mul_one, hcol]
          rw [block_embed, normal_one]
          have hcm : Measurable (fun A : Mat n => fun i => A i ⟨0, by omega⟩) :=
            measurable_pi_lambda _ fun i => meas_entry measurable_id i _
          rw [← gM_map_col n ⟨0, by omega⟩, Measure.map_apply hcm ((measurable_ext n) hB)]
          rfl
        · simp [h]
      · have hK' : K ≤ n := by omega
        have h413 : HasResidualLaw n K hK' := (lemma_4_13 n (K+1) (by omega) (by omega)).1
        obtain ⟨⟨c, hc, hcF⟩, hrl⟩ := h413
        have hF : Measurable (fun A : Mat n => firstColumns hK' A) :=
          measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => meas_entry measurable_id _ _
        refine step n K (firstColumns hK') hF c hc hcF ?_ IH
        intro H B hH hB
        have h0 : 0 < n - K := by omega
        have hcm : Measurable (fun M : Mat (n-K) => ext (n-K) (fun i => M i ⟨0, h0⟩)) :=
          (measurable_ext _).comp (measurable_pi_lambda _ fun i => meas_entry measurable_id i _)
        have : gM n {A | firstColumns hK' A ∈ H ∧
              residual A K ∈ (fun M : Mat (n-K) => ext (n-K) (fun i => M i ⟨0, h0⟩)) ⁻¹' B} =
            ∫⁻ A in {A : Mat n | firstColumns hK' A ∈ H}, columnsLaw (block (actualCov A K) (n-K)) (n-K)
              ((fun M : Mat (n-K) => ext (n-K) (fun i => M i ⟨0, h0⟩)) ⁻¹' B) ∂gM n :=
          hrl H _ hH (hcm hB)
        have hset : {A : Mat n | firstColumns hK' A ∈ H ∧ actualColumn A K ∈ B} =
            {A | firstColumns hK' A ∈ H ∧
              residual A K ∈ (fun M : Mat (n-K) => ext (n-K) (fun i => M i ⟨0, h0⟩)) ⁻¹' B} := by
          ext A; simp only [Set.mem_setOf_eq, Set.mem_preimage, actualColumn_eq A K (by omega)]
        rw [hset]
        refine this.trans (setLIntegral_congr_fun ?_ (fun A _ => ?_))
        · exact hF hH
        · have hcol : Measurable (fun M : Mat (n-K) => fun i => M i ⟨0, h0⟩) :=
            measurable_pi_lambda _ fun i => meas_entry measurable_id i _
          rw [hcF A, ← columnsLaw_map_col _ (n-K) ⟨0, h0⟩, Measure.map_apply hcol ((measurable_ext _) hB)]
          rfl

/-! ### Laws of Gaussian submatrices and their Gram determinants -/

/-- Restricting an i.i.d. product measure to injectively indexed coordinates. -/
lemma pi_map_restrict {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (r : ι' → ι)
    (hr : Function.Injective r) :
    (Measure.pi (fun _ : ι => μ)).map (fun x j => x (r j)) = Measure.pi (fun _ : ι' => μ) := by
  have hm : Measurable (fun (x : ι → α) j => x (r j)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  refine (Measure.pi_eq fun s hs => ?_).symm
  set s' : ι → Set α := fun i => {a | ∀ j, r j = i → a ∈ s j}
  have hpre : (fun (x : ι → α) j => x (r j)) ⁻¹' Set.univ.pi s = Set.univ.pi s' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, s', Set.mem_setOf_eq]
    constructor
    · intro h i j hj; subst hj; exact h j
    · intro h j; exact h (r j) j rfl
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image r)) ?_,
    Finset.prod_image (fun a _ b _ h => hr h)]
  · refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    ext a
    simp only [s', Set.mem_setOf_eq]
    exact ⟨fun h => h j rfl, fun h j' hj' => by rw [hr hj']; exact h⟩
  · intro i _ hi
    have : s' i = Set.univ := by
      ext a
      simp only [s', Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro j hj
      exact absurd (Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩) hi
    rw [this, measure_univ]

lemma gM_map_sub (n a b : ℕ) (r : Fin a → Fin n) (hr : Function.Injective r)
    (c : Fin b → Fin n) (hc : Function.Injective c) :
    (gM n).map (fun A => (fun i j => A (r i) (c j) : Fin a → Fin b → ℝ)) =
      GaussianMatrix.gaussianMatrix a b := by
  have h1 : Measurable (fun (A : Fin n → Fin n → ℝ) i => A (r i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have h2 : Measurable (fun (B : Fin a → Fin n → ℝ) => (fun i j => B i (c j) : Fin a → Fin b → ℝ)) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply _).comp (measurable_pi_apply _)
  change (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0 1).map
    (fun A : Fin n → Fin n → ℝ => fun i j => A (r i) (c j)) = _
  have : (fun A : Fin n → Fin n → ℝ => (fun i j => A (r i) (c j) : Fin a → Fin b → ℝ)) =
      (fun B : Fin a → Fin n → ℝ => (fun i j => B i (c j) : Fin a → Fin b → ℝ)) ∘
        (fun A i => A (r i)) := rfl
  rw [this, ← Measure.map_map h2 h1, pi_map_restrict _ r hr]
  have h3 := Measure.pi_map_pi (μ := fun _ : Fin a => Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (f := fun (_ : Fin a) (y : Fin n → ℝ) (j : Fin b) => y (c j))
    (fun _ => (measurable_pi_lambda _ fun j => measurable_pi_apply _).aemeasurable)
  rw [h3]
  unfold GaussianMatrix.gaussianMatrix
  congr 1
  funext i
  exact pi_map_restrict _ c hc

lemma measurable_det_gram (a b : ℕ) :
    Measurable (fun B : Fin a → Fin b → ℝ => ((Matrix.of B)ᵀ * Matrix.of B).det) := by
  simp only [Matrix.det_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  fun_prop

/-- `det(BᵀB)` for an `a × b` standard Gaussian `B` is a product of independent chi-squares. -/
lemma gauss_det_law (a b : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    (GaussianMatrix.gaussianMatrix a b).map
        (fun B : Fin a → Fin b → ℝ => ((Matrix.of B)ᵀ * Matrix.of B).det) =
      (Measure.pi (fun i : Fin b => chiSquare (a - i.val))).map (fun x => ∏ i, x i) := by
  rw [← lemma_4_10 b a hb hba]
  unfold wishart columnsLaw
  rw [normal_one]
  have hT : Measurable (fun z : Fin a → Vec b => (fun i j => z j i : Matrix (Fin b) (Fin a) ℝ)) := by
    change Measurable (fun z : Fin a → Vec b => fun i j => z j i)
    fun_prop
  have hG : Measurable (fun G : Matrix (Fin b) (Fin a) ℝ => G * G.transpose) := by
    change Measurable (fun G : Fin b → Fin a → ℝ => fun i j => ∑ k, G i k * G j k)
    fun_prop
  have hdet : Measurable (fun M : Mat b => M.det) := by
    change Measurable (fun M : Fin b → Fin b → ℝ => (Matrix.of M).det)
    simp only [Matrix.det_apply, Matrix.of_apply]
    fun_prop
  rw [Measure.map_map hG hT, Measure.map_map hdet (hG.comp hT)]
  rfl

/-! ### Chi-square facts -/

lemma chiSquare_neg (k : ℕ) : chiSquare k {x | x < 0} = 0 := by
  unfold chiSquare
  rw [Measure.map_apply (s := {x : ℝ | x < 0}) (by fun_prop) measurableSet_Iio]
  have : (fun x : Fin k → ℝ => ∑ i, x i ^ 2) ⁻¹' {x | x < 0} = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    positivity
  simp [this]

lemma chiSquare_nonpos (k : ℕ) (hk : 0 < k) : chiSquare k {x | x ≤ 0} = 0 := by
  haveI := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  unfold chiSquare
  rw [Measure.map_apply (s := {x : ℝ | x ≤ 0}) (by fun_prop) measurableSet_Iic]
  refine measure_mono_null (fun x hx => ?_) (Measure.pi_hyperplane _ ⟨0, hk⟩ 0)
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
  have h := Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg (x i))
    (Finset.mem_univ ⟨0, hk⟩)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm (h.trans hx) (sq_nonneg _))

lemma chiSquare_lintegral_abs (k : ℕ) (hk : 0 < k) :
    ∫⁻ x, ENNReal.ofReal |x| ∂chiSquare k = k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨hint, heq⟩ := lemma_4_8 k hk 1 (by linarith)
  have hae : (fun x => Real.rpow x 1) =ᵐ[chiSquare k] fun x => |x| := by
    have : ∀ᵐ x ∂chiSquare k, 0 ≤ x := by
      rw [ae_iff]; simpa [not_le] using chiSquare_neg k
    filter_upwards [this] with x hx
    simp [abs_of_nonneg hx]
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.congr hae) (ae_of_all _ fun x => abs_nonneg x),
    ← integral_congr_ae hae, heq]
  have hG : 0 < Real.Gamma ((k : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : Real.rpow 2 1 = 2 := Real.rpow_one 2
  rw [h2, add_comm, Real.Gamma_add_one (by positivity)]
  rw [show 2 * ((k : ℝ) / 2 * Real.Gamma ((k : ℝ) / 2)) / Real.Gamma ((k : ℝ) / 2) = k by
    field_simp]
  exact ENNReal.ofReal_natCast k

lemma chiSquare_lintegral_rpow_neg_half (k : ℕ) (hk : 2 ≤ k) :
    ∫⁻ x, (ENNReal.ofReal x) ^ (-(1/2 : ℝ)) ∂chiSquare k =
      ENNReal.ofReal (Real.rpow 2 (-(1/2)) * Real.Gamma (-(1/2) + (k : ℝ)/2) /
        Real.Gamma ((k : ℝ)/2)) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨hint, heq⟩ := lemma_4_8 k (by omega) (-(1/2)) (by linarith)
  have hpos : ∀ᵐ x ∂chiSquare k, 0 < x := by
    rw [ae_iff]; simpa [not_lt] using chiSquare_nonpos k (by omega)
  rw [← heq, ofReal_integral_eq_lintegral_ofReal hint
    (by filter_upwards [hpos] with x hx; exact Real.rpow_nonneg hx.le _)]
  refine lintegral_congr_ae ?_
  filter_upwards [hpos] with x hx
  rw [ENNReal.ofReal_rpow_of_pos hx]
  rfl

lemma chiSquare_one_le (s : ℝ) (hs : 0 < s) :
    chiSquare 1 {x | x ≤ s} ≤ ENNReal.ofReal (Real.sqrt s * Real.sqrt (2 / Real.pi)) := by
  unfold chiSquare
  rw [Measure.map_apply (s := {x : ℝ | x ≤ s}) (by fun_prop) measurableSet_Iic]
  have : (fun x : Fin 1 → ℝ => ∑ i, x i ^ 2) ⁻¹' {x | x ≤ s} =
      (fun x : Fin 1 → ℝ => x 0) ⁻¹' {y | |y| ≤ Real.sqrt s} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Fin.sum_univ_one]
    rw [← Real.sqrt_sq_eq_abs, Real.sqrt_le_sqrt_iff hs.le]
  have hm : MeasurableSet {y : ℝ | |y| ≤ Real.sqrt s} := measurableSet_le (by fun_prop) measurable_const
  rw [this, ← Measure.map_apply (measurable_pi_apply 0) hm,
    (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq]
  have h := lemma_4_2 (Real.sqrt s) (Real.sqrt_pos.2 hs)
  unfold prob at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

/-- Small-ball bound for a product of independent chi-squares `χ²_{L+1}, …, χ²_1`: condition on
all factors but the `χ²_1` one and use the Gaussian small-interval bound. -/
lemma prod_chi_small (L : ℕ) (z : ℝ) (hz : 0 < z) :
    (Measure.pi (fun i : Fin (L+1) => chiSquare (L+1 - i.val))) {x | ∏ i, x i ≤ z} ≤
      ENNReal.ofReal (Real.sqrt z * Real.sqrt (2 / Real.pi)) *
        ∏ j : Fin L, ENNReal.ofReal (Real.rpow 2 (-(1/2)) *
          Real.Gamma (-(1/2) + ((L+1-j.val : ℕ) : ℝ)/2) / Real.Gamma (((L+1-j.val : ℕ) : ℝ)/2)) := by
  set μ : Fin (L+1) → Measure ℝ := fun i => chiSquare (L+1 - i.val)
  have hmp := measurePreserving_piFinSuccAbove μ (Fin.last L)
  set S' : Set (ℝ × (Fin L → ℝ)) := {p | p.1 * ∏ j, p.2 j ≤ z}
  have hS' : MeasurableSet S' := measurableSet_le (by fun_prop) measurable_const
  have hpre : {x : Fin (L+1) → ℝ | ∏ i, x i ≤ z} =
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last L)) ⁻¹' S' := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, S']
    rw [Fin.prod_univ_succAbove _ (Fin.last L)]
    rfl
  rw [hpre, hmp.measure_preimage hS'.nullMeasurableSet, Measure.prod_apply_symm hS']
  have hlast : μ (Fin.last L) = chiSquare 1 := by simp [μ]
  have pw : ∀ w : Fin L → ℝ, chiSquare 1 ((fun y => (y, w)) ⁻¹' S') ≤
      ENNReal.ofReal (Real.sqrt z * Real.sqrt (2 / Real.pi)) *
        ∏ j, (ENNReal.ofReal (w j)) ^ (-(1/2 : ℝ)) := by
    intro w
    by_cases hw : ∀ j, 0 < w j
    · have hQ : 0 < ∏ j, w j := Finset.prod_pos fun j _ => hw j
      have hset : (fun y => (y, w)) ⁻¹' S' = {y | y ≤ z / ∏ j, w j} := by
        ext y; simp [S', le_div_iff₀ hQ]
      rw [hset]
      refine (chiSquare_one_le _ (div_pos hz hQ)).trans (le_of_eq ?_)
      have hprod : (∏ j, (ENNReal.ofReal (w j)) ^ (-(1/2 : ℝ))) =
          ENNReal.ofReal (∏ j, (w j) ^ (-(1/2 : ℝ))) := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.rpow_nonneg (hw j).le _)]
        exact Finset.prod_congr rfl fun j _ => ENNReal.ofReal_rpow_of_pos (hw j)
      rw [hprod, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.finsetProd_rpow _ _ (fun j _ => (hw j).le), Real.rpow_neg hQ.le,
        ← Real.sqrt_eq_rpow, Real.sqrt_div hz.le]
      field_simp
    · push_neg at hw
      obtain ⟨j, hj⟩ := hw
      have htop : ∏ j, (ENNReal.ofReal (w j)) ^ (-(1/2 : ℝ)) = ⊤ := by
        refine WithTop.prod_eq_top (Finset.mem_univ j) ?_ (fun i _ => ?_)
        · rw [ENNReal.ofReal_of_nonpos hj]; exact ENNReal.zero_rpow_of_neg (by norm_num)
        · intro h
          have h' : (ENNReal.ofReal (w i)) ^ (-(1/2 : ℝ)) = (0 : ℝ≥0∞) := h
          rw [ENNReal.rpow_eq_zero_iff] at h'
          rcases h' with ⟨_, h⟩ | ⟨h, _⟩
          · norm_num at h
          · exact ENNReal.ofReal_ne_top h
      have hc : ENNReal.ofReal (Real.sqrt z * Real.sqrt (2 / Real.pi)) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        have := Real.pi_pos
        positivity
      rw [htop, ENNReal.mul_top hc]
      exact le_top
  have hmeas : ∀ j : Fin L, Measurable (fun y : ℝ => (ENNReal.ofReal y) ^ (-(1/2 : ℝ))) :=
    fun _ => by fun_prop
  calc ∫⁻ w, μ (Fin.last L) ((fun y => (y, w)) ⁻¹' S') ∂(Measure.pi fun j => μ ((Fin.last L).succAbove j))
      ≤ ∫⁻ w, ENNReal.ofReal (Real.sqrt z * Real.sqrt (2 / Real.pi)) *
          ∏ j, (ENNReal.ofReal (w j)) ^ (-(1/2 : ℝ))
          ∂(Measure.pi fun j => μ ((Fin.last L).succAbove j)) :=
        lintegral_mono fun w => by rw [hlast]; exact pw w
    _ = ENNReal.ofReal (Real.sqrt z * Real.sqrt (2 / Real.pi)) *
          ∏ j, ∫⁻ y, (ENNReal.ofReal y) ^ (-(1/2 : ℝ)) ∂(μ ((Fin.last L).succAbove j)) := by
        rw [lintegral_const_mul _ (by fun_prop),
          lintegral_fintype_prod_eq_prod (fun _ y => (ENNReal.ofReal y) ^ (-(1/2 : ℝ))) hmeas]
    _ = _ := by
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [μ, Fin.succAbove_last, Fin.coe_castSucc]
        exact chiSquare_lintegral_rpow_neg_half _ (by omega)

/-- The chi-square negative half moments telescope. -/
lemma tele (L : ℕ) :
    ∏ j : Fin L, (Real.rpow 2 (-(1/2)) * Real.Gamma (-(1/2) + ((L+1-j.val : ℕ) : ℝ)/2) /
      Real.Gamma (((L+1-j.val : ℕ) : ℝ)/2)) =
      Real.rpow 2 (-(L:ℝ)/2) * Real.Gamma (1/2) / Real.Gamma (((L+1 : ℕ) : ℝ)/2) := by
  induction L with
  | zero =>
    have : 0 < Real.Gamma (2⁻¹) := Real.Gamma_pos_of_pos (by norm_num)
    simp [div_self this.ne']
  | succ L ih =>
    rw [Fin.prod_univ_succ]
    have e : ∀ j : Fin L, ((L+1+1 - (Fin.succ j).val : ℕ) : ℝ) = ((L+1 - j.val : ℕ) : ℝ) := by
      intro j; congr 1; simp only [Fin.val_succ]; omega
    simp_rw [e]
    rw [ih]
    simp only [Fin.val_zero, Nat.sub_zero]
    have hΓ1 : 0 < Real.Gamma (((L+1 : ℕ) : ℝ)/2) := Real.Gamma_pos_of_pos (by positivity)
    have hΓ2 : 0 < Real.Gamma (((L+1+1 : ℕ) : ℝ)/2) := Real.Gamma_pos_of_pos (by positivity)
    have h1 : -(1/2 : ℝ) + ((L+1+1 : ℕ) : ℝ)/2 = ((L+1 : ℕ) : ℝ)/2 := by push_cast; ring
    have h2 : Real.rpow 2 (-(1/2)) * Real.rpow 2 (-(L:ℝ)/2) = Real.rpow 2 (-((L+1 : ℕ) : ℝ)/2) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add (by norm_num)]
      congr 1; push_cast; ring
    rw [h1, ← h2]
    field_simp

/-- `Γ(K/2)² K² 2^K ≥ K!`. -/
lemma gamma_half_sq (K : ℕ) (hK : 1 ≤ K) :
    (K.factorial : ℝ) ≤ Real.Gamma ((K:ℝ)/2) ^ 2 * (K:ℝ) ^ 2 * 2 ^ K := by
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    rcases (show K = 1 ∨ K = 2 ∨ 3 ≤ K by omega) with rfl | rfl | h3
    · have : Real.Gamma (((1:ℕ):ℝ)/2) ^ 2 = Real.pi := by
        rw [show ((1:ℕ):ℝ)/2 = 1/2 by norm_num, Real.Gamma_one_half_eq,
          Real.sq_sqrt Real.pi_pos.le]
      rw [this]; norm_num; linarith [Real.pi_gt_three]
    · rw [show ((2:ℕ):ℝ)/2 = 1 by norm_num, Real.Gamma_one]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, K = m + 2 := ⟨K-2, by omega⟩
      have hm := ih m (by omega) (by omega)
      have hΓ : Real.Gamma (((m+2:ℕ):ℝ)/2) = ((m:ℝ)/2) * Real.Gamma ((m:ℝ)/2) := by
        rw [show ((m+2:ℕ):ℝ)/2 = (m:ℝ)/2 + 1 by push_cast; ring,
          Real.Gamma_add_one (by have : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
                                 positivity)]
      rw [hΓ, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      have hf : (0:ℝ) ≤ (m.factorial : ℝ) := by positivity
      have hm0 : (0:ℝ) ≤ m := by positivity
      calc ((m:ℝ) + 1 + 1) * (((m:ℝ) + 1) * (m.factorial : ℝ))
          ≤ (m.factorial : ℝ) * ((m:ℝ) + 2) ^ 2 := by nlinarith
        _ ≤ (Real.Gamma ((m:ℝ)/2) ^ 2 * (m:ℝ) ^ 2 * 2 ^ m) * ((m:ℝ) + 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hm (by positivity)
        _ = ((m:ℝ)/2 * Real.Gamma ((m:ℝ)/2)) ^ 2 * ((m:ℝ) + 2) ^ 2 * 2 ^ (m + 2) := by ring


end GEPP414


namespace GEPP414

open GEPPGrowth.Main

/-! ### The pivot minor is a row-permuted `K × K` submatrix -/

lemma labels_injective {n : ℕ} (A : Mat n) : ∀ t, Function.Injective (run A t).labels
  | 0 => by simpa [run] using Function.injective_id
  | t+1 => by
    rw [run]
    split_ifs with h
    · exact (labels_injective A t).comp (Equiv.injective _)
    · exact labels_injective A t

/-- Rows `J` (in increasing order) and the first `K` columns of `A`. -/
def subJ {n K : ℕ} (hK : K ≤ n) (J : Finset (Fin n)) (hJ : J.card = K) (A : Mat n) : Mat K :=
  fun i j => A (J.orderEmbOfFin hJ i) (Fin.castLE hK j)

lemma pivotMinor_sq {n K : ℕ} (hK : K ≤ n) (A : Mat n) :
    ∃ J : Finset (Fin n), ∃ hJ : J.card = K,
      (pivotMinor hK A).det ^ 2 = (subJ hK J hJ A).det ^ 2 := by
  classical
  set σ : Fin K → Fin n := fun i => (run A K).labels ⟨i.val, by omega⟩
  have hσ : Function.Injective σ := by
    intro i i' h
    have := labels_injective A K h
    exact Fin.ext (by simpa using this)
  set J := Finset.univ.image σ
  have hJ : J.card = K := by
    rw [Finset.card_image_of_injective _ hσ, Finset.card_univ, Fintype.card_fin]
  refine ⟨J, hJ, ?_⟩
  set e := J.orderIsoOfFin hJ
  set π : Fin K → Fin K := fun i => e.symm ⟨σ i, Finset.mem_image_of_mem σ (Finset.mem_univ i)⟩
  have hπ : ∀ i, J.orderEmbOfFin hJ (π i) = σ i := by
    intro i
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [π, e]
  have hπi : Function.Injective π := by
    intro i i' h
    apply hσ
    rw [← hπ i, ← hπ i', h]
  set P : Equiv.Perm (Fin K) := Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπi)
  have hM : pivotMinor hK A = (subJ hK J hJ A).submatrix P id := by
    ext i j
    simp only [pivotMinor, subJ, Matrix.submatrix_apply, id, P, Equiv.ofBijective_apply, hπ]
    rfl
  rw [hM, Matrix.det_permute, mul_pow]
  rcases Int.units_eq_one_or (Equiv.Perm.sign P) with h | h <;> simp [h]

/-! ### Tail bounds for the numerator and the denominator -/

lemma measurable_det (K : ℕ) : Measurable (fun M : Mat K => M.det) := by
  change Measurable (fun M : Fin K → Fin K → ℝ => (Matrix.of M).det)
  simp only [Matrix.det_apply, Matrix.of_apply]
  fun_prop

/-- Markov's inequality for `det(FᵀF)`, `F` the first `K` columns. -/
lemma num_tail (n K : ℕ) (hK0 : 0 < K) (hK : K ≤ n) (s : ℝ) (hs : 0 < s) :
    gM n {A | s ≤ ((firstColumns hK A).transpose * firstColumns hK A).det} ≤
      ENNReal.ofReal (∏ i : Fin K, ((n - i.val : ℕ) : ℝ)) / ENNReal.ofReal s := by
  have hsub := gM_map_sub n n K id Function.injective_id (Fin.castLE hK) (Fin.castLE_injective hK)
  have hmB : Measurable (fun A : Mat n => (fun i j => A (id i) (Fin.castLE hK j) : Fin n → Fin K → ℝ)) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => meas_entry measurable_id _ _
  have hset : {A : Mat n | s ≤ ((firstColumns hK A).transpose * firstColumns hK A).det} =
      (fun A : Mat n => (fun i j => A (id i) (Fin.castLE hK j) : Fin n → Fin K → ℝ)) ⁻¹'
        ((fun B : Fin n → Fin K → ℝ => ((Matrix.of B)ᵀ * Matrix.of B).det) ⁻¹' {x | s ≤ x}) := rfl
  have hI : MeasurableSet {x : ℝ | s ≤ x} := measurableSet_Ici
  rw [hset, ← Measure.map_apply hmB ((measurable_det_gram n K) hI), hsub,
    ← Measure.map_apply (measurable_det_gram n K) hI, gauss_det_law n K hK0 hK,
    Measure.map_apply (by fun_prop) hI]
  set μ := Measure.pi (fun i : Fin K => chiSquare (n - i.val))
  have hsub2 : (fun x : Fin K → ℝ => ∏ i, x i) ⁻¹' {x | s ≤ x} ⊆
      {x | ENNReal.ofReal s ≤ ∏ i, ENNReal.ofReal |x i|} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (hx.trans ?_)
    rw [← Finset.abs_prod]; exact le_abs_self _
  refine (measure_mono hsub2).trans ?_
  have hmeasP : Measurable (fun x : Fin K → ℝ => ∏ i, ENNReal.ofReal |x i|) := by fun_prop
  refine (meas_ge_le_lintegral_div hmeasP.aemeasurable (by simpa using hs)
    ENNReal.ofReal_ne_top).trans ?_
  rw [lintegral_fintype_prod_eq_prod (fun _ x => ENNReal.ofReal |x|) (fun _ => by fun_prop)]
  gcongr
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  refine le_of_eq (Finset.prod_congr rfl fun i _ => ?_)
  rw [chiSquare_lintegral_abs _ (by omega), ENNReal.ofReal_natCast]

/-- Union bound over the `C(n, K)` row sets, then the chi-square small-ball bound. -/
lemma den_small (n L : ℕ) (hL : L + 1 ≤ n) (z : ℝ) (hz : 0 < z) :
    gM n {A | (pivotMinor hL A).det ^ 2 ≤ z} ≤
      (n.choose (L+1) : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt z * Real.sqrt (2 / Real.pi)) *
        ∏ j : Fin L, ENNReal.ofReal (Real.rpow 2 (-(1/2)) *
          Real.Gamma (-(1/2) + ((L+1-j.val : ℕ) : ℝ)/2) / Real.Gamma (((L+1-j.val : ℕ) : ℝ)/2))) := by
  classical
  set T : Finset (Fin n) → Set (Mat n) :=
    fun J => {A | ∃ hJ : J.card = L+1, (subJ hL J hJ A).det ^ 2 ≤ z}
  have hcover : {A : Mat n | (pivotMinor hL A).det ^ 2 ≤ z} ⊆
      ⋃ J ∈ Finset.univ.powersetCard (L+1), T J := by
    intro A hA
    obtain ⟨J, hJ, he⟩ := pivotMinor_sq hL A
    simp only [Set.mem_setOf_eq] at hA
    refine Set.mem_biUnion (x := J) ?_ ⟨hJ, he ▸ hA⟩
    simp [Finset.mem_powersetCard, hJ]
  refine (measure_mono hcover).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hone : ∀ J ∈ Finset.univ.powersetCard (L+1), gM n (T J) ≤
      ENNReal.ofReal (Real.sqrt z * Real.sqrt (2 / Real.pi)) *
        ∏ j : Fin L, ENNReal.ofReal (Real.rpow 2 (-(1/2)) *
          Real.Gamma (-(1/2) + ((L+1-j.val : ℕ) : ℝ)/2) /
            Real.Gamma (((L+1-j.val : ℕ) : ℝ)/2)) := by
    intro J hJmem
    have hJ : J.card = L+1 := (Finset.mem_powersetCard.1 hJmem).2
    have hTJ : T J = (fun A : Mat n =>
        (fun i j => A (J.orderEmbOfFin hJ i) (Fin.castLE hL j) : Fin (L+1) → Fin (L+1) → ℝ)) ⁻¹'
          ((fun B : Fin (L+1) → Fin (L+1) → ℝ => ((Matrix.of B)ᵀ * Matrix.of B).det) ⁻¹'
            Set.Iic z) := by
      ext A
      simp only [T, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
      rw [Matrix.det_mul, Matrix.det_transpose, ← sq]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hJ, h⟩⟩
    have hmB : Measurable (fun A : Mat n =>
        (fun i j => A (J.orderEmbOfFin hJ i) (Fin.castLE hL j) : Fin (L+1) → Fin (L+1) → ℝ)) :=
      measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => meas_entry measurable_id _ _
    rw [hTJ, ← Measure.map_apply hmB ((measurable_det_gram _ _) measurableSet_Iic),
      gM_map_sub n (L+1) (L+1) _ (J.orderEmbOfFin hJ).injective _ (Fin.castLE_injective hL),
      ← Measure.map_apply (measurable_det_gram _ _) measurableSet_Iic,
      gauss_det_law (L+1) (L+1) (by omega) le_rfl,
      Measure.map_apply (by fun_prop) measurableSet_Iic]
    exact prod_chi_small L z hz
  refine (Finset.sum_le_sum hone).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end GEPP414

namespace GEPP414
open GEPPGrowth.Main

/-! ### Choosing the split and the arithmetic -/

/-- With `z = N / (2 M t^{2/3})`, `N/(t z) + U √z ≤ 4 M / t^{1/3}` as soon as `U² N ≤ 8 M³`. -/
lemma optimize (N U M t : ℝ) (hN : 0 < N) (hU : 0 ≤ U) (hM : 0 < M) (ht : 0 < t)
    (hUN : U ^ 2 * N ≤ 8 * M ^ 3) :
    ∃ z > 0, N / (t * z) + U * Real.sqrt z ≤ 4 * M / Real.rpow t (1/3) := by
  set w := Real.rpow t (1/3) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos ht _
  have hw3 : w ^ 3 = t := by
    rw [hw, Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
  refine ⟨N / (2 * M * w ^ 2), by positivity, ?_⟩
  have h1 : N / (t * (N / (2 * M * w ^ 2))) = 2 * M / w := by
    rw [← hw3]; field_simp
  have h2 : U * Real.sqrt (N / (2 * M * w ^ 2)) ≤ 2 * M / w := by
    have hl : 0 ≤ U * Real.sqrt (N / (2 * M * w ^ 2)) := by positivity
    have hr : 0 ≤ 2 * M / w := by positivity
    refine (pow_le_pow_iff_left₀ hl hr (by norm_num : (2:ℕ) ≠ 0)).1 ?_
    rw [mul_pow, Real.sq_sqrt (by positivity), div_pow]
    have e : U ^ 2 * (N / (2 * M * w ^ 2)) = (U ^ 2 * N) / (2 * M) / w ^ 2 := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : 4 * M / w = 2 * M / w + 2 * M / w := by ring
  rw [h1, h4]
  linarith

lemma prod_sub_eq (n K : ℕ) :
    (∏ i : Fin K, ((n - i.val : ℕ) : ℝ)) = (K.factorial : ℝ) * (n.choose K : ℝ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => ((n - i : ℕ) : ℝ)), ← Nat.cast_prod,
    ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast; ring

lemma UN_bound (L d : ℕ) (hd : 1 ≤ d) :
    ((((L+1+d).choose (L+1) : ℕ) : ℝ) * (Real.sqrt (2 / Real.pi) *
        (Real.rpow 2 (-(L:ℝ)/2) * Real.Gamma (1/2) / Real.Gamma (((L+1:ℕ):ℝ)/2)))) ^ 2 *
      (∏ i : Fin (L+1), ((L+1+d - i.val : ℕ) : ℝ)) ≤ 8 * (((L+1+d : ℕ) : ℝ) ^ (d+1)) ^ 3 := by
  set n := L + 1 + d with hn
  set C : ℝ := ((n.choose (L+1) : ℕ) : ℝ)
  set g := Real.Gamma (((L+1:ℕ):ℝ)/2)
  have hg : 0 < g := Real.Gamma_pos_of_pos (by positivity)
  have hr : (Real.rpow 2 (-(L:ℝ)/2)) ^ 2 * 2 ^ L = 1 := by
    rw [Real.rpow_eq_pow, ← Real.rpow_natCast ((2:ℝ) ^ (-(L:ℝ)/2)) 2,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2:ℝ) L, ← Real.rpow_add (by norm_num),
      show (-(L:ℝ)/2) * ((2:ℕ):ℝ) + (L:ℝ) = 0 by push_cast; ring, Real.rpow_zero]
  have hpi : Real.Gamma (1/2) ^ 2 = Real.pi := by
    rw [Real.Gamma_one_half_eq, Real.sq_sqrt Real.pi_pos.le]
  have hs : Real.sqrt (2 / Real.pi) ^ 2 = 2 / Real.pi := Real.sq_sqrt (by positivity)
  have hfac := gamma_half_sq (L+1) (by omega)
  have hC0 : 0 ≤ C := by positivity
  have hCn : C ≤ (n:ℝ) ^ d := by
    have h1 : (n.choose (L+1) : ℝ) = (n.choose d : ℝ) := by
      rw [show L + 1 = n - d by omega, Nat.choose_symm (by omega)]
    have h2 := Nat.choose_le_pow_div (α := ℝ) d n
    have h3 : (n:ℝ) ^ d / (d.factorial : ℝ) ≤ (n:ℝ) ^ d :=
      div_le_self (by positivity) (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero d))
    simp only [C]; rw [h1]; exact h2.trans h3
  have hKn : ((L+1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : L + 1 ≤ n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  rw [prod_sub_eq]
  -- U² N = 2 C³ (L+1)! / (2^L g²)
  have hU2 : (C * (Real.sqrt (2 / Real.pi) * (Real.rpow 2 (-(L:ℝ)/2) * Real.Gamma (1/2) / g))) ^ 2 *
      (((L+1).factorial : ℝ) * C) = 2 * C ^ 3 * ((L+1).factorial : ℝ) / (2 ^ L * g ^ 2) := by
    have hpi0 : Real.pi ≠ 0 := Real.pi_pos.ne'
    have h2L : (2:ℝ) ^ L ≠ 0 := by positivity
    have hrr : (Real.rpow 2 (-(L:ℝ)/2)) ^ 2 = 1 / 2 ^ L := by
      rw [eq_div_iff h2L]; exact hr
    rw [show (C * (Real.sqrt (2 / Real.pi) * (Real.rpow 2 (-(L:ℝ)/2) * Real.Gamma (1/2) / g))) ^ 2
      = C ^ 2 * Real.sqrt (2 / Real.pi) ^ 2 * (Real.rpow 2 (-(L:ℝ)/2)) ^ 2 * Real.Gamma (1/2) ^ 2
        / g ^ 2 by ring, hs, hrr, hpi]
    field_simp
  rw [hU2]
  have hstep : 2 * C ^ 3 * ((L+1).factorial : ℝ) / (2 ^ L * g ^ 2) ≤
      2 * C ^ 3 * (g ^ 2 * ((L+1:ℕ):ℝ) ^ 2 * 2 ^ (L+1)) / (2 ^ L * g ^ 2) := by
    gcongr
  refine hstep.trans ?_
  have e : 2 * C ^ 3 * (g ^ 2 * ((L+1:ℕ):ℝ) ^ 2 * 2 ^ (L+1)) / (2 ^ L * g ^ 2) =
      4 * C ^ 3 * ((L+1:ℕ):ℝ) ^ 2 := by
    field_simp
    ring
  rw [e]
  have hC3 : C ^ 3 ≤ ((n:ℝ) ^ d) ^ 3 := pow_le_pow_left₀ hC0 hCn 3
  have hK2 : ((L+1:ℕ):ℝ) ^ 2 ≤ (n:ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hKn 2
  have hn3 : (n:ℝ) ^ 2 ≤ 2 * (n:ℝ) ^ 3 := by nlinarith
  calc 4 * C ^ 3 * ((L+1:ℕ):ℝ) ^ 2 ≤ 4 * ((n:ℝ) ^ d) ^ 3 * (n:ℝ) ^ 2 := by gcongr
    _ ≤ 4 * ((n:ℝ) ^ d) ^ 3 * (2 * (n:ℝ) ^ 3) := by gcongr
    _ = 8 * ((n:ℝ) ^ (d+1)) ^ 3 := by ring

end GEPP414

namespace GEPP414
open GEPPGrowth.Main

/-- The all-threshold tail bound. -/
lemma tail (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (t : ℝ) (ht : 0 < t) :
    prob (covLaw n (k-1)) {S | t ≤ (block S (n-(k-1))).det} ≤
      4 * (n:ℝ)^((n-k+1)+1) / Real.rpow t (1/3) := by
  have h413 := (lemma_4_13 n k hk hkn).2
  obtain ⟨L, rfl⟩ : ∃ L, k = L + 2 := ⟨k - 2, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = L + 1 + d := ⟨n - (L+1), by omega⟩
  have hd : 1 ≤ d := by omega
  rw [show L + 1 + d - (L + 2) + 1 = d by omega]
  change prob (covLaw (L+1+d) (L+1)) {S | t ≤ (block S (L+1+d-(L+1))).det} ≤ _
  change ∀ᵐ A ∂(gM (L+1+d)), (block (actualCov A (L+1)) (L+1+d-(L+1))).det =
      ((firstColumns (show L+1 ≤ L+1+d by omega) A).transpose *
        firstColumns (show L+1 ≤ L+1+d by omega) A).det /
      (pivotMinor (show L+1 ≤ L+1+d by omega) A).det ^ 2 at h413
  set n := L + 1 + d with hn
  have hK : L + 1 ≤ n := by omega
  set num : Mat n → ℝ := fun A => ((firstColumns hK A).transpose * firstColumns hK A).det
  set den : Mat n → ℝ := fun A => (pivotMinor hK A).det
  set N : ℝ := ∏ i : Fin (L+1), ((n - i.val : ℕ) : ℝ)
  set C : ℝ := ((n.choose (L+1) : ℕ) : ℝ)
  set β : ℝ := Real.rpow 2 (-(L:ℝ)/2) * Real.Gamma (1/2) / Real.Gamma (((L+1:ℕ):ℝ)/2)
  set U : ℝ := C * (Real.sqrt (2 / Real.pi) * β)
  have hβ : 0 < β := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/2)
    have := Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < ((L+1:ℕ):ℝ)/2)
    have : 0 < Real.rpow 2 (-(L:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hN : 0 < N := by
    simp only [N]
    rw [prod_sub_eq]
    have : 0 < n.choose (L+1) := Nat.choose_pos hK
    positivity
  have hU : 0 ≤ U := by positivity
  have hM : (0:ℝ) < (n:ℝ) ^ (d+1) := by
    have : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  obtain ⟨z, hz, hzb⟩ := optimize N U ((n:ℝ) ^ (d+1)) t hN hU hM ht (UN_bound L d hd)
  -- the measure bound
  have hE : MeasurableSet {S : CovState | t ≤ (block S (n-(L+1))).det} :=
    measurableSet_le measurable_const ((measurable_det _).comp (measurable_block _))
  have h1 := coupling n (L+1) (by omega) _ hE
  have h2 : gM n {A | actualCov A (L+1) ∈ {S : CovState | t ≤ (block S (n-(L+1))).det}} =
      gM n {A | t ≤ num A / den A ^ 2} := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [h413] with A hA
    simp only [Set.mem_setOf_eq, num, den]
    rw [hA]
  have h3 : {A : Mat n | t ≤ num A / den A ^ 2} ⊆
      {A | t * z ≤ num A} ∪ {A | den A ^ 2 ≤ z} := by
    intro A hA
    simp only [Set.mem_setOf_eq, Set.mem_union] at hA ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨hnum, hden⟩ := hcon
    have hd2 : 0 < den A ^ 2 := hz.trans hden
    have : num A / den A ^ 2 < t := by
      rw [div_lt_iff₀ hd2]
      calc num A < t * z := hnum
        _ < t * den A ^ 2 := by gcongr
    linarith
  have h4 := num_tail n (L+1) (by omega) hK (t * z) (by positivity)
  have h5 := den_small n L hK z hz
  have hprodβ : (∏ j : Fin L, ENNReal.ofReal (Real.rpow 2 (-(1/2)) *
        Real.Gamma (-(1/2) + ((L+1-j.val : ℕ) : ℝ)/2) / Real.Gamma (((L+1-j.val : ℕ) : ℝ)/2))) =
      ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_prod_of_nonneg, tele]
    intro j _
    have := Real.Gamma_pos_of_pos (show (0:ℝ) < ((L+1-j.val : ℕ) : ℝ)/2 by
      have : 2 ≤ L + 1 - j.val := by omega
      have : (2:ℝ) ≤ ((L+1-j.val : ℕ) : ℝ) := by exact_mod_cast this
      linarith)
    have := Real.Gamma_pos_of_pos (show (0:ℝ) < -(1/2) + ((L+1-j.val : ℕ) : ℝ)/2 by
      have : 2 ≤ L + 1 - j.val := by omega
      have : (2:ℝ) ≤ ((L+1-j.val : ℕ) : ℝ) := by exact_mod_cast this
      linarith)
    have : 0 < Real.rpow 2 (-(1/2)) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hmain : covLaw n (L+1) {S : CovState | t ≤ (block S (n-(L+1))).det} ≤
      ENNReal.ofReal (N / (t * z) + U * Real.sqrt z) := by
    refine (h1.trans (le_of_eq h2)).trans ((measure_mono h3).trans
      ((measure_union_le _ _).trans ?_))
    refine (add_le_add h4 h5).trans (le_of_eq ?_)
    rw [hprodβ, ← ENNReal.ofReal_div_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp only [U, C]
    ring
  unfold prob
  exact (ENNReal.toReal_le_of_le_ofReal (by positivity) hmain).trans hzb

end GEPP414

open GEPPGrowth.Main in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (∀ t : ℝ, 0 < t →
      prob (covLaw n (k-1)) {S | t ≤ (block S (n-(k-1))).det} ≤
        4 * (n:ℝ)^((n-k+1)+1) / Real.rpow t (1/3)) ∧
    prob (covLaw n (k-1)) {S | 512 * (n:ℝ)^(3*(n-k+1)+3) ≤
      (block S (n-(k-1))).det} ≤ 1/2 := by
  refine ⟨fun t ht => GEPP414.tail n k hk hkn t ht, ?_⟩
  have hn : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set e := n - k + 1
  have ht : (0:ℝ) < 512 * (n:ℝ)^(3*e+3) := by positivity
  refine (GEPP414.tail n k hk hkn _ ht).trans (le_of_eq ?_)
  have hcube : Real.rpow (512 * (n:ℝ)^(3*e+3)) (1/3) = 8 * (n:ℝ)^(e+1) := by
    rw [show 512 * (n:ℝ)^(3*e+3) = (8 * (n:ℝ)^(e+1)) ^ (3:ℕ) by ring, Real.rpow_eq_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hcube]
  field_simp
  ring
