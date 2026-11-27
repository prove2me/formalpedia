-- Prove2me | solution 1 for GEPPGrowth.Main.large_growth_probability
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:58:30.227793+00:00
-- url     : https://prove2.me/submissions/25ef6fd1-9bbb-4e71-8bae-9489b2685616

import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_GEPPGrowth_Main_lemma_4_13
import Theorems.Thm_GEPPGrowth_Main_lemma_4_3
import Theorems.Thm_GEPPGrowth_Main_proposition_5_3
import Theorems.Thm_GEPPGrowth_Main_proposition_5_4

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


end GEPP414

/-! ## Theorem 2.2 -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPPMain

open GEPPGrowth.Main GEPP414

/-- The growth level reached with parameter `r` (the paper's `f(r)`, with `T = 20`):
`√((7/5)^r max(N_{r+20}, 1) / 42) / (3 r √(log n))`. -/
def thr (n r : ℕ) : ℝ :=
  Real.sqrt ((7/5:ℝ)^r * max (initialNormBound n (r+20)) 1 / 42) / (3 * r * Real.sqrt (Real.log n))

/-- Proposition 5.3's lower bound on `Pr(G_r)` with `T = 20`, `d = r + 20`. -/
def B (n r : ℕ) : ℝ :=
  (1/2 - 1/(n:ℝ)) * (0.16:ℝ) ^ ((r:ℝ)*((r:ℝ)+43)/2) /
    ((32*Real.sqrt 2)^r * ((r:ℝ)+21) ^ ((r:ℝ)*((r:ℝ)+3)/4) * (n:ℝ) ^ (3*(r:ℝ)*((r:ℝ)+22)/2))

/-- Union bound of Lemma 4.3 over the `n` rows, at level `s = 3 r √(log n)`. -/
def tail (n r : ℕ) : ℝ :=
  (n:ℝ)^2 * Real.sqrt 2 / ((3 * r * Real.sqrt (Real.log n)) * Real.sqrt Real.pi) *
    Real.exp (-(3 * r * Real.sqrt (Real.log n))^2/2)

/-! ### Probability part -/

open scoped Matrix.Norms.L2Operator in
lemma measurable_specNorm_block (m : ℕ) :
    Measurable (fun S : CovState => GaussianMatrix.specNorm (block S m)) := by
  unfold GaussianMatrix.specNorm
  exact continuous_norm.measurable.comp (by unfold block; fun_prop)

lemma B_le (n r : ℕ) (hrn : r + 22 ≤ n) :
    B n r ≤ prob (covLaw n (n - 21))
      {S | (7/5:ℝ)^r ≤ GaussianMatrix.specNorm (block S 21) / max (initialNormBound n (r + 20)) 1} := by
  have h := proposition_5_3 n 20 (r+20) (by norm_num) (by omega) (by omega)
  simp only at h
  rw [show r + 20 - 20 = r by omega] at h
  rw [show n - (r + 20) + r - 1 = n - 21 by omega, show n - (n-21) = 21 by omega] at h
  norm_num at h
  refine le_trans (le_of_eq ?_) h
  unfold B
  norm_num
  ring_nf

lemma growth_ge {n : ℕ} (A : Mat n) (a s : ℝ) (ha : 0 < a) (hU : a ≤ maxEntry (upper A))
    (hA : maxEntry A < s) : a / s ≤ growth A := by
  have hA0 : 0 ≤ maxEntry A := NNReal.coe_nonneg _
  have hpos : 0 < maxEntry A := by
    rcases hA0.lt_or_eq with h | h
    · exact h
    exfalso
    have hz : A = 0 := by
      ext i j
      have : ‖A i j‖₊ ≤ (Finset.univ : Finset (Fin n × Fin n)).sup (fun ij => ‖A ij.1 ij.2‖₊) :=
        Finset.le_sup (f := fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) (Finset.mem_univ (i, j))
      have h0 : (((Finset.univ : Finset (Fin n × Fin n)).sup (fun ij => ‖A ij.1 ij.2‖₊) : NNReal) : ℝ)
          = 0 := h.symm
      have h0' := NNReal.coe_eq_zero.1 h0
      have : ‖A i j‖₊ = 0 := le_antisymm (this.trans (le_of_eq h0')) (zero_le)
      simpa using this
    have hrun : ∀ t, (run A t).matrix = 0 := by
      intro t
      induction t with
      | zero => simp [run, hz]
      | succ t ih =>
        simp only [run]
        split_ifs
        · ext a b; simp [stepAt, ih]
        · exact ih
    have hU0 : maxEntry (upper A) = 0 := by
      have : upper A = 0 := by ext i j; simp [upper, hrun]
      rw [this]; simp [maxEntry]
    linarith
  unfold growth
  exact div_le_div₀ (ha.le.trans hU) hU hpos hA.le

lemma tail_le (n r : ℕ) (hn : 0 < n) (hr : 0 < r) (hl : 0 < Real.log n) :
    prob (GaussianMatrix.gaussianMatrix n n) {A : Mat n | 3 * r * Real.sqrt (Real.log n) ≤ maxEntry A}
      ≤ tail n r := by
  set s := 3 * (r:ℝ) * Real.sqrt (Real.log n) with hs
  have hs0 : 0 < s := by positivity
  set R : Set (Fin n → ℝ) := {x | s ≤ maxEntry (fun i (_ : Fin 1) => x i)} with hR
  set b := (n:ℝ) * Real.sqrt 2 / (s * Real.sqrt Real.pi) * Real.exp (-s^2/2) with hb
  have hb0 : 0 ≤ b := by positivity
  have h43 : Measure.pi (fun _ : Fin n => gaussianReal 0 1) R ≤ ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (lemma_4_3 n hn s hs0)
  have hsub : {A : Mat n | s ≤ maxEntry A} ⊆ ⋃ i : Fin n, (fun A : Fin n → Fin n → ℝ => A i) ⁻¹' R := by
    intro A hA
    simp only [Set.mem_setOf_eq] at hA
    have hne : (Finset.univ : Finset (Fin n × Fin n)).Nonempty := ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
    obtain ⟨⟨i, j⟩, -, hij⟩ := Finset.exists_mem_eq_sup _ hne (fun ij => ‖A ij.1 ij.2‖₊)
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    simp only [Set.mem_preimage, hR, Set.mem_setOf_eq]
    refine hA.trans ?_
    unfold maxEntry
    rw [hij]
    exact_mod_cast Finset.le_sup (f := fun kl : Fin n × Fin 1 => ‖A i kl.1‖₊) (Finset.mem_univ (j, 0))
  have hrow : ∀ i : Fin n, GaussianMatrix.gaussianMatrix n n ((fun A : Fin n → Fin n → ℝ => A i) ⁻¹' R)
      ≤ ENNReal.ofReal b := by
    intro i
    refine (Measure.le_map_apply (f := fun A : Fin n → Fin n → ℝ => A i)
      (measurable_pi_apply i).aemeasurable R).trans ?_
    unfold GaussianMatrix.gaussianMatrix
    rw [(measurePreserving_eval (fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0 1) i).map_eq]
    exact h43
  have hμ : GaussianMatrix.gaussianMatrix n n {A : Mat n | s ≤ maxEntry A} ≤ ENNReal.ofReal (n * b) := by
    calc _ ≤ GaussianMatrix.gaussianMatrix n n (⋃ i : Fin n, (fun A : Fin n → Fin n → ℝ => A i) ⁻¹' R) :=
          measure_mono hsub
      _ ≤ ∑ i : Fin n, GaussianMatrix.gaussianMatrix n n ((fun A : Fin n → Fin n → ℝ => A i) ⁻¹' R) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal b := Finset.sum_le_sum fun i _ => hrow i
      _ = ENNReal.ofReal (n * b) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hμ).trans (le_of_eq ?_)
  rw [hb]; unfold tail; rw [← hs]; ring

lemma core (n r : ℕ) (hr : 1 ≤ r) (hrn : r + 22 ≤ n) :
    0.47 * B n r - tail n r ≤ prob (GaussianMatrix.gaussianMatrix n n) {A | thr n r ≤ growth A} := by
  set μ := GaussianMatrix.gaussianMatrix n n with hμ
  set M := max (initialNormBound n (r + 20)) 1 with hM
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  set g := (7/5:ℝ)^r * M with hg
  have hg0 : 0 < g := by positivity
  set E : Set CovState := {S | g ≤ GaussianMatrix.specNorm (block S 21)} with hE
  have hEm : MeasurableSet E := measurableSet_le measurable_const (measurable_specNorm_block 21)
  -- `Pr(G_r) ≥ B` for the actual GEPP covariance, through the coupling
  have hG : B n r ≤ prob μ {A | g ≤ GaussianMatrix.specNorm (block (actualCov A (n - 21)) 21)} := by
    refine (B_le n r hrn).trans ?_
    have hset : {S : CovState | (7/5:ℝ)^r ≤ GaussianMatrix.specNorm (block S 21) / M} = E := by
      ext S; simp only [Set.mem_setOf_eq, hE, hg, le_div_iff₀ hM0]
    rw [hset]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (coupling n (n - 21) (by omega) E hEm)
  have hBpos : 0 < B n r := by
    unfold B
    have : (0:ℝ) < 1/2 - 1/(n:ℝ) := by
      have : (22:ℝ) ≤ n := by exact_mod_cast (by omega : 22 ≤ n)
      have : 1/(n:ℝ) ≤ 1/22 := one_div_le_one_div_of_le (by norm_num) this
      linarith
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact div_pos (mul_pos this (Real.rpow_pos_of_pos (by norm_num) _))
      (mul_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos (by positivity) _))
        (Real.rpow_pos_of_pos hn0 _))
  -- Proposition 5.4
  have h54 := proposition_5_4 n 21 (by norm_num) (by omega) g hg0 (hBpos.trans_le hG)
  norm_num at h54
  rw [le_div_iff₀ (hBpos.trans_le hG)] at h54
  set a := Real.sqrt g / Real.sqrt 42 with ha
  set s := 3 * (r:ℝ) * Real.sqrt (Real.log n) with hs
  have hthr : thr n r = a / s := by
    unfold thr; rw [ha, hs, Real.sqrt_div' _ (by norm_num)]
  have ha0 : 0 < a := by positivity
  -- `{max |U| ≥ a} ⊆ {growth ≥ a/s} ∪ {max |A| ≥ s}`
  have hsub : {A : Mat n | a ≤ maxEntry (upper A) ∧
      g ≤ GaussianMatrix.specNorm (block (actualCov A (n - 21)) 21)} ⊆
      {A : Mat n | thr n r ≤ growth A} ∪ {A : Mat n | s ≤ maxEntry A} := by
    intro A ⟨hU, _⟩
    by_cases hA : s ≤ maxEntry A
    · exact Or.inr hA
    · exact Or.inl (by rw [hthr]; exact growth_ge A a s ha0 hU (lt_of_not_ge hA))
  have hU : prob μ {A : Mat n | a ≤ maxEntry (upper A) ∧
      g ≤ GaussianMatrix.specNorm (block (actualCov A (n - 21)) 21)} ≤
      prob μ {A : Mat n | thr n r ≤ growth A} + prob μ {A : Mat n | s ≤ maxEntry A} := by
    unfold prob
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (by finiteness) ((measure_mono hsub).trans (measure_union_le _ _))
  have hT := tail_le n r (by omega) (by omega) (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
  have hB047 : 0.47 * B n r ≤ 47/100 * prob μ {A | g ≤ GaussianMatrix.specNorm (block (actualCov A (n - 21)) 21)} := by
    norm_num; linarith
  rw [← hμ] at h54 hT
  rw [← hs] at hT
  have e1 := (hB047.trans h54).trans hU
  have final : 0.47 * B n r - tail n r ≤ prob μ {A : Mat n | thr n r ≤ growth A} := by
    have := add_le_add_left hT (prob μ {A : Mat n | thr n r ≤ growth A})
    linarith
  exact final

/-! ### Numerics -/

lemma exp_0_23112 : Real.exp 0.23112 ≤ 1.2601 := by
  have := Real.exp_bound' (x := 0.23112) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

lemma exp_4_8 : Real.exp 4.8 ≤ 122 := by
  have h1 := Real.exp_bound' (x := 0.8) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1
  have h2 := Real.exp_one_lt_d9
  have e : Real.exp 4.8 = Real.exp 0.8 * Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have h3 : Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le h2.le 4
  nlinarith [Real.exp_pos 0.8, Real.exp_pos 1]

lemma exp_1_121 : Real.exp (1 + 1/121) ≤ 2.7409 := by
  have h1 := Real.exp_bound' (x := 1/121) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1
  have h2 := Real.exp_one_lt_d9
  rw [Real.exp_add]
  nlinarith [Real.exp_pos (1/121), Real.exp_pos 1]

lemma exp_1_8333 : 6.25 ≤ Real.exp 1.8333 := by
  have := Real.sum_le_exp_of_nonneg (x := 1.8333) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

lemma pow_ind (m : ℕ) (hm : 100 ≤ m) :
    0.0275 * (m:ℝ)^2 * ((m:ℝ) + 30.6) * 1.2601^m ≤ 1.4^m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk' : (100:ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    have hp : (0:ℝ) < 1.2601^k := by positivity
    have poly : 1.2601 * (((k:ℝ)+1)^2 * ((k:ℝ) + 1 + 30.6)) ≤ 1.4 * ((k:ℝ)^2 * ((k:ℝ) + 30.6)) := by
      nlinarith [mul_pos (by linarith : (0:ℝ) < k) (by linarith : (0:ℝ) < k)]
    calc 0.0275 * ((k:ℝ)+1)^2 * ((k:ℝ) + 1 + 30.6) * 1.2601^(k+1)
        = 0.0275 * 1.2601^k * (1.2601 * (((k:ℝ)+1)^2 * ((k:ℝ) + 1 + 30.6))) := by ring
      _ ≤ 0.0275 * 1.2601^k * (1.4 * ((k:ℝ)^2 * ((k:ℝ) + 30.6))) := by gcongr
      _ = 1.4 * (0.0275 * (k:ℝ)^2 * ((k:ℝ) + 30.6) * 1.2601^k) := by ring
      _ ≤ 1.4 * 1.4^k := by gcongr
      _ = 1.4^(k+1) := by ring


lemma log_n_ge {n : ℕ} (hn : 122 ≤ n) : 4.8 ≤ Real.log n := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact exp_4_8.trans (by exact_mod_cast hn)

lemma tail_num (n r : ℕ) (hr : 100 ≤ r) (hrn : r + 22 ≤ n) :
    tail n r ≤ Real.exp (-2.37 * (r:ℝ)^2 * Real.log n) := by
  have hl := log_n_ge (by omega : 122 ≤ n)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 : (100:ℝ) ≤ r := by exact_mod_cast hr
  set ℓ := Real.log n with hℓ
  unfold tail
  rw [← hℓ]
  have hl0 : 0 < ℓ := by linarith
  have hsl : 1 ≤ Real.sqrt ℓ := by rw [Real.one_le_sqrt]; linarith
  have hsp : 1 ≤ Real.sqrt Real.pi := by rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have hs2 : Real.sqrt 2 ≤ 1.5 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hc : Real.sqrt 2 / ((3 * r * Real.sqrt ℓ) * Real.sqrt Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (300:ℝ) ≤ 3 * r * Real.sqrt ℓ := by nlinarith
    nlinarith
  have hsq : (3 * (r:ℝ) * Real.sqrt ℓ)^2 = 9 * (r:ℝ)^2 * ℓ := by
    rw [mul_pow, Real.sq_sqrt hl0.le]; ring
  have hn2 : (n:ℝ)^2 = Real.exp (2 * ℓ) := by
    rw [hℓ, show 2 * Real.log n = ((2:ℕ):ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
      Real.exp_log hn0]
  rw [hsq, mul_div_assoc, hn2]
  calc Real.exp (2 * ℓ) * (Real.sqrt 2 / ((3 * r * Real.sqrt ℓ) * Real.sqrt Real.pi)) *
        Real.exp (-(9 * (r:ℝ)^2 * ℓ) / 2)
      ≤ Real.exp (2 * ℓ) * 1 * Real.exp (-(9 * (r:ℝ)^2 * ℓ) / 2) := by gcongr
    _ = Real.exp (2 * ℓ - 9 * (r:ℝ)^2 * ℓ / 2) := by rw [mul_one, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-2.37 * (r:ℝ)^2 * ℓ) := by
        apply Real.exp_le_exp.2
        have : (10000:ℝ) ≤ (r:ℝ)^2 := by nlinarith
        nlinarith

lemma P_num (n r : ℕ) (hr : 100 ≤ r) (hrn : r + 22 ≤ n) :
    Real.exp (-2.37 * (r:ℝ)^2 * Real.log n) ≤ 0.47 * B n r - tail n r := by
  have hl := log_n_ge (by omega : 122 ≤ n)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 : (100:ℝ) ≤ r := by exact_mod_cast hr
  have hrn' : (r:ℝ) + 21 ≤ n := by exact_mod_cast (by omega : r + 21 ≤ n)
  set ℓ := Real.log n with hℓ
  set x : ℝ := (r:ℝ)*((r:ℝ)+43)/2 with hx
  set y : ℝ := (r:ℝ)*((r:ℝ)+3)/4 with hy
  set z : ℝ := 3*(r:ℝ)*((r:ℝ)+22)/2 with hz
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hz0 : 0 ≤ z := by positivity
  -- numerator: `0.16^x ≥ exp(-1.8333 x)`
  have h016 : Real.exp (-1.8333 * x) ≤ (0.16:ℝ) ^ x := by
    have hb : Real.exp (-1.8333) ≤ 0.16 := by
      rw [Real.exp_neg]
      have := exp_1_8333
      rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    calc Real.exp (-1.8333 * x) = Real.exp (-1.8333) ^ x := Real.exp_mul _ _
      _ ≤ (0.16:ℝ) ^ x := Real.rpow_le_rpow (Real.exp_pos _).le hb hx0
  -- denominator: `(32√2)^r (r+21)^y n^z ≤ exp(3.8124 r + ℓ (y+z))`
  have h32 : (32 * Real.sqrt 2) ^ r ≤ Real.exp (3.8124 * r) := by
    have hlog : Real.log (32 * Real.sqrt 2) ≤ 3.8124 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by norm_num),
        show (32:ℝ) = 2^5 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9
      push_cast; linarith
    have hb : 32 * Real.sqrt 2 ≤ Real.exp 3.8124 := by
      rw [← Real.exp_log (by positivity : (0:ℝ) < 32 * Real.sqrt 2)]
      exact Real.exp_le_exp.2 hlog
    calc (32 * Real.sqrt 2) ^ r ≤ Real.exp 3.8124 ^ r := pow_le_pow_left₀ (by positivity) hb r
      _ = Real.exp (3.8124 * r) := by rw [← Real.exp_nat_mul]; ring_nf
  have h21 : ((r:ℝ)+21) ^ y ≤ (n:ℝ) ^ y := Real.rpow_le_rpow (by positivity) hrn' hy0
  have hnyz : (n:ℝ) ^ y * (n:ℝ) ^ z = Real.exp (ℓ * (y + z)) := by
    rw [← Real.rpow_add hn0, Real.rpow_def_of_pos hn0]
  have hD : (32 * Real.sqrt 2)^r * ((r:ℝ)+21) ^ y * (n:ℝ) ^ z ≤
      Real.exp (3.8124 * r + ℓ * (y + z)) := by
    rw [Real.exp_add, ← hnyz, mul_assoc]
    gcongr
  have hD0 : 0 < (32 * Real.sqrt 2)^r * ((r:ℝ)+21) ^ y * (n:ℝ) ^ z :=
    mul_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos hn0 _)
  have hhalf : (0.49:ℝ) ≤ 1/2 - 1/(n:ℝ) := by
    have : (122:ℝ) ≤ n := by exact_mod_cast (by omega : 122 ≤ n)
    have : 1/(n:ℝ) ≤ 1/122 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hB : 0.49 * Real.exp (-1.8333 * x - (3.8124 * r + ℓ * (y + z))) ≤ B n r := by
    unfold B
    rw [← hx, ← hy, ← hz, Real.exp_sub, mul_div_assoc]
    gcongr
  -- the exponent
  have hW : -2.37 * (r:ℝ)^2 * ℓ + 3 ≤ -1.8333 * x - (3.8124 * r + ℓ * (y + z)) := by
    rw [hx, hy, hz]
    have h1 : 0 ≤ (ℓ - 4.8) * (0.62 * (r:ℝ) - 33.75) * r :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have h2 : 0 ≤ ((r:ℝ) - 100) * r := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have he3 : 10 ≤ Real.exp 3 := by
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3
    rw [h3]; norm_num at h; linarith
  have hmain : 2 * Real.exp (-2.37 * (r:ℝ)^2 * ℓ) ≤ 0.47 * B n r := by
    have hlow : Real.exp (-2.37 * (r:ℝ)^2 * ℓ) * Real.exp 3 ≤
        Real.exp (-1.8333 * x - (3.8124 * r + ℓ * (y + z))) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 hW
    have hE := Real.exp_pos (-2.37 * (r:ℝ)^2 * ℓ)
    nlinarith
  -- the tail
  have htail := tail_num n r hr hrn
  linarith

lemma thr_top (n : ℕ) (hn : 122 ≤ n) :
    Real.rpow (7/5:ℝ) (((n:ℝ)-22)/2) / (3 * Real.sqrt 42 * ((n:ℝ)-22) * Real.sqrt (Real.log n))
      ≤ thr n (n - 22) := by
  have hk : ((n - 22 : ℕ) : ℝ) = (n:ℝ) - 22 := by
    rw [Nat.cast_sub (by omega : 22 ≤ n)]; norm_num
  have hl := log_n_ge hn
  have hk0 : (0:ℝ) < (n:ℝ) - 22 := by
    have : (122:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set P : ℝ := (7/5:ℝ)^(n-22) with hP
  have e : Real.rpow (7/5:ℝ) (((n:ℝ)-22)/2) = Real.sqrt P := by
    rw [Real.rpow_eq_pow, Real.sqrt_eq_rpow, hP, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hk]
    ring_nf
  unfold thr
  rw [e, hk]
  have h42 : Real.sqrt P / Real.sqrt 42 = Real.sqrt (P / 42) := (Real.sqrt_div' _ (by norm_num)).symm
  calc Real.sqrt P / (3 * Real.sqrt 42 * ((n:ℝ)-22) * Real.sqrt (Real.log n))
      = Real.sqrt (P / 42) / (3 * ((n:ℝ)-22) * Real.sqrt (Real.log n)) := by
        rw [← h42]; field_simp
    _ ≤ _ := by
        gcongr
        calc P = P * 1 := by ring
          _ ≤ _ := by gcongr; exact le_max_right _ _

/-- `L ≥ 0.05778 (m+1)` when `ρ` exceeds `thr n m` as well as `100 √n log n`. -/
lemma L_step (n m : ℕ) (hn : 122 ≤ n) (hm : 100 ≤ m) (hmn : m + 23 ≤ n) (ρ : ℝ)
    (hlo : 100 * Real.sqrt (n:ℝ) * Real.log n ≤ ρ) (hthr : thr n m < ρ) :
    0.05778 * ((m:ℝ) + 1) ≤ Real.log (ρ / Real.sqrt n) := by
  have hl := log_n_ge hn
  have hn0 : (0:ℝ) < n := by positivity
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hm0 : (100:ℝ) ≤ m := by exact_mod_cast hm
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) hlo
  have hu : 0 < ρ / Real.sqrt n := div_pos hρ hs
  have hu1 : 100 * Real.log n ≤ ρ / Real.sqrt n := by rw [le_div_iff₀ hs]; linarith
  have hthr0 : 0 ≤ thr n m := by unfold thr; positivity
  have hu2 : thr n m / Real.sqrt n ≤ ρ / Real.sqrt n := div_le_div_of_nonneg_right hthr.le hs.le
  rw [Real.le_log_iff_exp_le hu]
  -- the squared form: `exp(0.05778 (m+1))² ≤ 100 log n · thr n m / √n`
  set ℓ := Real.log n with hℓ
  set X := Real.exp (1 + 1 / (((m + 20 : ℕ) : ℝ) + 1)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have hXle : X ≤ 2.7409 := by
    refine (Real.exp_le_exp.2 ?_).trans exp_1_121
    have : (121:ℝ) ≤ ((m + 20 : ℕ) : ℝ) + 1 := by push_cast; linarith
    have : 1 / (((m + 20 : ℕ) : ℝ) + 1) ≤ 1 / 121 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  set a := (7/5:ℝ)^m * max (initialNormBound n (m+20)) 1 / 42 with ha
  have hNa : (7/5:ℝ)^m * (n / (X * ((m:ℝ) + 21 + 2 * ℓ))) / 42 ≤ a := by
    rw [ha]; gcongr
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    unfold initialNormBound; rw [hX, hℓ]; push_cast; ring
  have hkey : Real.exp 0.23112 ^ (m+1) * (378 * (m:ℝ)^2 * X * ((m:ℝ) + 21 + 2 * ℓ)) ≤
      10^4 * ℓ * (7/5:ℝ)^m := by
    have h1 : Real.exp 0.23112 ^ (m+1) ≤ 1.2601 ^ (m+1) :=
      pow_le_pow_left₀ (Real.exp_pos _).le exp_0_23112 _
    have h2 : 4.8 * ((m:ℝ) + 21 + 2 * ℓ) ≤ ℓ * ((m:ℝ) + 30.6) := by nlinarith
    have h3 := pow_ind m hm
    have hp : (0:ℝ) < 1.2601^m := by positivity
    calc Real.exp 0.23112 ^ (m+1) * (378 * (m:ℝ)^2 * X * ((m:ℝ) + 21 + 2 * ℓ))
        ≤ 1.2601 ^ (m+1) * (378 * (m:ℝ)^2 * 2.7409 * ((m:ℝ) + 21 + 2 * ℓ)) := by
          gcongr
      _ = (1.2601 * 378 * 2.7409 / 4.8) * (1.2601^m * (m:ℝ)^2) * (4.8 * ((m:ℝ) + 21 + 2 * ℓ)) := by
          ring
      _ ≤ (1.2601 * 378 * 2.7409 / 4.8) * (1.2601^m * (m:ℝ)^2) * (ℓ * ((m:ℝ) + 30.6)) := by
          gcongr
      _ = (1.2601 * 378 * 2.7409 / 4.8 / 0.0275) * ℓ * (0.0275 * (m:ℝ)^2 * ((m:ℝ) + 30.6) * 1.2601^m) := by
          ring
      _ ≤ (1.2601 * 378 * 2.7409 / 4.8 / 0.0275) * ℓ * (7/5:ℝ)^m := by
          gcongr; norm_num at h3 ⊢; linarith
      _ ≤ 10^4 * ℓ * (7/5:ℝ)^m := by gcongr; norm_num
  have hsq : (100 * ℓ * (thr n m / Real.sqrt n))^2 = 10^4 * ℓ * a / (9 * (m:ℝ)^2 * n) := by
    have hl0 : 0 < ℓ := by linarith
    unfold thr
    rw [← ha, ← hℓ, show (100 * ℓ * (Real.sqrt a / (3 * m * Real.sqrt ℓ) / Real.sqrt n))^2 =
      10^4 * ℓ^2 * (Real.sqrt a)^2 / (9 * (m:ℝ)^2 * (Real.sqrt ℓ)^2 * (Real.sqrt n)^2) by ring,
      Real.sq_sqrt (by positivity), Real.sq_sqrt hl0.le, Real.sq_sqrt hn0.le]
    field_simp
  have hE4 : (Real.exp (0.05778 * ((m:ℝ) + 1)) ^ 2) ^ 2 ≤ (100 * ℓ * (thr n m / Real.sqrt n))^2 := by
    rw [hsq, ← pow_mul, ← Real.exp_nat_mul, show ((2 * 2 : ℕ) : ℝ) * (0.05778 * ((m:ℝ) + 1)) =
      ((m + 1 : ℕ) : ℝ) * 0.23112 by push_cast; ring, Real.exp_nat_mul]
    have hm1 : (0:ℝ) < m := by linarith
    rw [le_div_iff₀ (by positivity)]
    calc Real.exp 0.23112 ^ (m+1) * (9 * (m:ℝ)^2 * n)
        = Real.exp 0.23112 ^ (m+1) * (378 * (m:ℝ)^2 * X * ((m:ℝ) + 21 + 2 * ℓ)) *
            (n / (X * ((m:ℝ) + 21 + 2 * ℓ)) / 42) := by
          field_simp; norm_num
      _ ≤ 10^4 * ℓ * (7/5:ℝ)^m * (n / (X * ((m:ℝ) + 21 + 2 * ℓ)) / 42) := by
          gcongr
      _ = 10^4 * ℓ * ((7/5:ℝ)^m * (n / (X * ((m:ℝ) + 21 + 2 * ℓ))) / 42) := by ring
      _ ≤ 10^4 * ℓ * a := by gcongr
  have hE2 : Real.exp (0.05778 * ((m:ℝ) + 1)) ^ 2 ≤ 100 * ℓ * (thr n m / Real.sqrt n) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hE4
  have hfin : Real.exp (0.05778 * ((m:ℝ) + 1)) ^ 2 ≤ (ρ / Real.sqrt n) ^ 2 := by
    refine hE2.trans ?_
    rw [sq]
    exact mul_le_mul hu1 hu2 (by positivity) hu.le
  exact (pow_le_pow_iff_left₀ (by positivity) hu.le two_ne_zero).1 hfin

lemma L_base (n : ℕ) (hn : 122 ≤ n) (ρ : ℝ) (hlo : 100 * Real.sqrt (n:ℝ) * Real.log n ≤ ρ) :
    0.05778 * (100:ℝ) ≤ Real.log (ρ / Real.sqrt n) := by
  have hl := log_n_ge hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
  have hu : 480 ≤ ρ / Real.sqrt n := by
    rw [le_div_iff₀ hs]; nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h6 : Real.exp 6 ≤ 2.7182818286 ^ 6 := by
    rw [show (6:ℝ) = ((6:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_d9.le 6
  have : Real.exp (0.05778 * 100) ≤ Real.exp 6 := Real.exp_le_exp.2 (by norm_num)
  have : (2.7182818286:ℝ) ^ 6 ≤ 480 := by norm_num
  linarith

/-- The paper's `r_ρ`: the least `r ≥ 100` with `thr n r ≥ ρ`. -/
lemma exists_r (n : ℕ) (hn : 122 ≤ n) (ρ : ℝ)
    (hlo : 100 * Real.sqrt (n:ℝ) * Real.log n ≤ ρ)
    (hhi : ρ ≤ Real.rpow (7/5:ℝ) (((n:ℝ)-22)/2) /
      (3 * Real.sqrt 42 * ((n:ℝ)-22) * Real.sqrt (Real.log n))) :
    ∃ r : ℕ, 100 ≤ r ∧ r + 22 ≤ n ∧ ρ ≤ thr n r ∧ 0.05778 * (r:ℝ) ≤ Real.log (ρ / Real.sqrt n) := by
  classical
  have hex : ∃ k, ρ ≤ thr n (k + 100) := ⟨n - 122, by
    rw [show n - 122 + 100 = n - 22 by omega]; exact hhi.trans (thr_top n hn)⟩
  have hkle : Nat.find hex ≤ n - 122 := Nat.find_min' hex (by
    rw [show n - 122 + 100 = n - 22 by omega]; exact hhi.trans (thr_top n hn))
  refine ⟨Nat.find hex + 100, by omega, by omega, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; simpa using L_base n hn ρ hlo
  · have hj : ¬ ρ ≤ thr n (Nat.find hex - 1 + 100) := Nat.find_min hex (by omega)
    have := L_step n (Nat.find hex - 1 + 100) hn (by omega) (by omega) ρ hlo (lt_of_not_ge hj)
    have e : ((Nat.find hex - 1 + 100 : ℕ):ℝ) + 1 = ((Nat.find hex + 100 : ℕ):ℝ) := by
      rw [← Nat.cast_succ]; congr 1; omega
    rwa [e] at this

end GEPPMain

open GEPPGrowth.Main GEPPMain in
theorem solution (n : ℕ) (hn : 122 ≤ n) (ρ : ℝ)
    (hlo : 100 * Real.sqrt (n:ℝ) * Real.log n ≤ ρ)
    (hhi : ρ ≤ Real.rpow (7/5:ℝ) (((n:ℝ)-22)/2) /
      (3 * Real.sqrt 42 * ((n:ℝ)-22) * Real.sqrt (Real.log n))) :
    Real.exp (-710 * (Real.log (ρ / Real.sqrt (n:ℝ)))^2 * Real.log n) ≤
      prob (GaussianMatrix.gaussianMatrix n n) {A | ρ ≤ growth A} := by
  have hl := log_n_ge hn
  obtain ⟨r, hr1, hr2, hkspec, hL⟩ := exists_r n hn ρ hlo hhi
  have hr0 : (0:ℝ) ≤ r := by positivity
  have hsq : 2.37 * (r:ℝ)^2 ≤ 710 * (Real.log (ρ / Real.sqrt n))^2 := by
    nlinarith [mul_self_le_mul_self (by positivity) hL]
  calc Real.exp (-710 * (Real.log (ρ / Real.sqrt (n:ℝ)))^2 * Real.log n)
      ≤ Real.exp (-2.37 * (r:ℝ)^2 * Real.log n) := by
        apply Real.exp_le_exp.2
        nlinarith
    _ ≤ 0.47 * B n r - tail n r := P_num n r (by omega) (by omega)
    _ ≤ prob (GaussianMatrix.gaussianMatrix n n) {A | thr n r ≤ growth A} := core n r (by omega) (by omega)
    _ ≤ prob (GaussianMatrix.gaussianMatrix n n) {A | ρ ≤ growth A} := by
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        exact measure_mono fun A hA => hkspec.trans hA
