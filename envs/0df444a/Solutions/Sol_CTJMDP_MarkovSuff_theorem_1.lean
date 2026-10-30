-- Prove2me | solution 1 for CTJMDP.MarkovSuff.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:41:49.363987+00:00
-- url     : https://prove2.me/submissions/40e17291-d659-4f53-a976-07b7457b4823
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting
import Definitions.Def_CTJMDP_MarkovSuff_Extension
import Theorems.Thm_CTJMDP_MarkovSuff_lemma_5
import Theorems.Thm_CTJMDP_MarkovSuff_eq_58_59
import Theorems.Thm_CTJMDP_MarkovSuff_ext_disintegrates
import Theorems.Thm_CTJMDP_MarkovSuff_law_exists_unique

open CTJMDP.MarkovSuff MeasureTheory Set
open scoped ENNReal

namespace CTJMDPAux


theorem sb_sum {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] : StandardBorelSpace (X ⊕ Y) := by
  let := upgradeStandardBorel X
  let := upgradeStandardBorel Y
  refine ⟨⟨inferInstance, ?_, inferInstance⟩⟩
  constructor
  apply le_antisymm
  · intro s hs
    have h1 : MeasurableSet[borel X] (Sum.inl ⁻¹' s : Set X) := by
      have := hs.1; rwa [eq_borel_upgradeStandardBorel X] at this
    have h2 : MeasurableSet[borel Y] (Sum.inr ⁻¹' s : Set Y) := by
      have := hs.2; rwa [eq_borel_upgradeStandardBorel Y] at this
    have e1 : (borel X) = MeasurableSpace.comap Sum.inl (borel (X ⊕ Y)) := by
      have := @borel_comap X (X ⊕ Y) Sum.inl instTopologicalSpaceSum
      rwa [← Topology.IsEmbedding.inl.eq_induced] at this
    have e2 : (borel Y) = MeasurableSpace.comap Sum.inr (borel (X ⊕ Y)) := by
      have := @borel_comap Y (X ⊕ Y) Sum.inr instTopologicalSpaceSum
      rwa [← Topology.IsEmbedding.inr.eq_induced] at this
    rw [e1] at h1
    rw [e2] at h2
    obtain ⟨C1, hC1, hC1e⟩ := h1
    obtain ⟨C2, hC2, hC2e⟩ := h2
    have : s = (C1 ∩ Set.range Sum.inl) ∪ (C2 ∩ Set.range Sum.inr) := by
      ext z; rcases z with z | z
      · have := congrArg (fun S => z ∈ S) hC1e; simp at this; simp [this]
      · have := congrArg (fun S => z ∈ S) hC2e; simp at this; simp [this]
    rw [this]
    exact @MeasurableSet.union _ (borel (X ⊕ Y)) _ _ (@MeasurableSet.inter _ (borel _) _ _ hC1 (MeasurableSpace.measurableSet_generateFrom isOpen_range_inl)) (@MeasurableSet.inter _ (borel _) _ _ hC2 (MeasurableSpace.measurableSet_generateFrom isOpen_range_inr))
  · apply MeasurableSpace.generateFrom_le
    intro U hU
    constructor
    · exact (hU.preimage continuous_inl).measurableSet
    · exact (hU.preimage continuous_inr).measurableSet


theorem meas_sum_prod {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (f : (α ⊕ β) × γ → δ)
    (h1 : Measurable (fun p : α × γ => f (Sum.inl p.1, p.2)))
    (h2 : Measurable (fun p : β × γ => f (Sum.inr p.1, p.2))) : Measurable f := by
  have : f = (fun q => Sum.elim (fun p : α × γ => f (Sum.inl p.1, p.2))
      (fun p : β × γ => f (Sum.inr p.1, p.2)) q) ∘ MeasurableEquiv.sumProdDistrib α β γ := by
    funext p; rcases p with ⟨a | b, c⟩ <;> rfl
  rw [this]; exact (h1.sumElim h2).comp (MeasurableEquiv.sumProdDistrib _ _ _).measurable

theorem meas_prod_sum {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (f : α × (β ⊕ γ) → δ)
    (h1 : Measurable (fun p : α × β => f (p.1, Sum.inl p.2)))
    (h2 : Measurable (fun p : α × γ => f (p.1, Sum.inr p.2))) : Measurable f := by
  have : f = (fun q => Sum.elim (fun p : α × β => f (p.1, Sum.inl p.2))
      (fun p : α × γ => f (p.1, Sum.inr p.2)) q) ∘ MeasurableEquiv.prodSumDistrib α β γ := by
    funext p; rcases p with ⟨a, b | c⟩ <;> rfl
  rw [this]; exact (h1.sumElim h2).comp (MeasurableEquiv.prodSumDistrib _ _ _).measurable

theorem memb_inl {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableEmbedding (Sum.inl : α → α ⊕ β) :=
  ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩



variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

theorem measurable_tn (n : ℕ) : Measurable (fun ω : Traj X => tn ω n) := by
  cases n with
  | zero => simp only [tn]; exact measurable_const
  | succ k => simp only [tn]; fun_prop

theorem measurable_xn (n : ℕ) : Measurable (fun ω : Traj X => xn ω n) := by
  cases n with
  | zero => simp only [xn]; fun_prop
  | succ k => simp only [xn]; fun_prop

theorem measurable_hist (n : ℕ) : Measurable (hist (X := X) n) := by
  unfold hist; fun_prop

theorem measurableSet_inInt (n : ℕ) (t : ℝ) : MeasurableSet {ω : Traj X | inInt ω n t} := by
  unfold inInt
  exact (measurableSet_lt (measurable_tn n) measurable_const).inter
    (measurableSet_le measurable_const (measurable_tn (n+1)))

theorem jumpMass_le_zero (M : Model X A) (π : Policy X A) (n : ℕ) (ω : Traj X) (r : ℝ≥0∞)
    (hr : r < tn ω n) : jumpMass M π n ω {c | c.1 ≤ r} = 0 := by
  have hC : MeasurableSet {c : ℝ≥0∞ × X | c.1 ≤ r} := measurableSet_le measurable_fst measurable_const
  unfold jumpMass
  split_ifs with h
  · rw [Measure.dirac_apply' _ hC]
    have : ¬ (⊤ ≤ r) := by rw [top_le_iff]; exact hr.ne_top
    simp [Set.indicator, this]
  · have h1 : ∀ s : ℝ, ∀ y : X, ({c : ℝ≥0∞ × X | c.1 ≤ r}.indicator (fun _ => (1 : ℝ≥0∞)) (tn ω n + ENNReal.ofReal s, y)) = 0 := by
      intro s y
      apply Set.indicator_of_notMem
      simp only [mem_ofPred_eq, not_le]
      exact lt_of_lt_of_le hr le_self_add
    have h2 : ({c : ℝ≥0∞ × X | c.1 ≤ r}.indicator (fun _ => (1 : ℝ≥0∞)) (⊤, xn ω n)) = 0 := by
      apply Set.indicator_of_notMem
      simp only [mem_ofPred_eq, top_le_iff]
      exact (lt_of_lt_of_le hr le_top).ne_top
    simp [h1, h2]

theorem tn_succ_ae (M : Model X A) (gam : Measure X) (π : Policy X A) (P : Measure (Traj X))
    (hP : IsLaw M gam π P) (n : ℕ) : ∀ᵐ ω ∂P, tn ω n ≤ tn ω (n + 1) := by
  cases n with
  | zero => exact Filter.Eventually.of_forall (fun ω => by simp [tn])
  | succ k =>
    have key : ∀ q : ℚ, P {ω | hist (k+1) ω ∈ {h : X × (Fin (k+1) → ℝ≥0∞ × X) |
        ENNReal.ofReal q < (h.2 (Fin.last k)).1} ∧ ω.2 (k+1) ∈ {c : ℝ≥0∞ × X | c.1 ≤ ENNReal.ofReal q}} = 0 := by
      intro q
      have hS : MeasurableSet {h : X × (Fin (k+1) → ℝ≥0∞ × X) |
          ENNReal.ofReal q < (h.2 (Fin.last k)).1} :=
        measurableSet_lt measurable_const (by fun_prop)
      rw [hP.step (k+1) _ _ hS (measurableSet_le measurable_fst measurable_const)]
      have hmeas : MeasurableSet {ω : Traj X | hist (k+1) ω ∈ {h : X × (Fin (k+1) → ℝ≥0∞ × X) |
          ENNReal.ofReal q < (h.2 (Fin.last k)).1}} := measurable_hist (k+1) hS
      rw [setLIntegral_congr_fun hmeas (g := fun _ => 0)]
      · simp
      · intro ω hω
        apply jumpMass_le_zero
        simpa [hist, tn] using hω
    rw [ae_iff]
    apply measure_mono_null _ (measure_iUnion_null key)
    intro ω hω
    simp only [not_le, mem_ofPred_eq] at hω
    obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hω
    simp only [mem_iUnion, mem_ofPred_eq]
    refine ⟨q, ?_, ?_⟩
    · exact hq2
    · exact hq1.le


theorem stateMarg_univ (P : Measure (Traj X)) (t : ℝ) :
    stateMarg P t univ = ∑' n, P {ω | inInt ω n t} := by
  unfold stateMarg
  rw [Measure.sum_apply _ MeasurableSet.univ]
  congr 1; funext n
  rw [Measure.map_apply (measurable_xn n) MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]

theorem stateMarg_univ_eq_union (M : Model X A) (gam : Measure X) (π : Policy X A)
    (P : Measure (Traj X)) (hP : IsLaw M gam π P) (t : ℝ) :
    stateMarg P t univ = P (⋃ n, {ω | inInt ω n t}) := by
  rw [stateMarg_univ, measure_iUnion₀]
  · intro n m hnm
    have hmono : ∀ᵐ ω ∂P, ∀ k, tn ω k ≤ tn ω (k + 1) :=
      ae_all_iff.2 (fun k => tn_succ_ae M gam π P hP k)
    refine measure_mono_null (t := {ω | ¬ ∀ k, tn ω k ≤ tn ω (k + 1)}) ?_ (ae_iff.1 hmono)
    intro ω ⟨h1, h2⟩
    simp only [mem_ofPred_eq, not_forall, not_le]
    by_contra hc
    push Not at hc
    have hm : Monotone (fun k => tn ω k) := monotone_nat_of_le_succ hc
    rcases lt_or_gt_of_ne hnm with h | h
    · exact lt_irrefl _ (lt_of_le_of_lt (le_trans h1.2 (hm (Nat.succ_le_of_lt h))) h2.1)
    · exact lt_irrefl _ (lt_of_le_of_lt (le_trans h2.2 (hm (Nat.succ_le_of_lt h))) h1.1)
  · exact fun n => (measurableSet_inInt n t).nullMeasurableSet

theorem stateMarg_univ_le_one (M : Model X A) (gam : Measure X) (π : Policy X A)
    (P : Measure (Traj X)) (hP : IsLaw M gam π P) (t : ℝ) :
    stateMarg P t univ ≤ 1 := by
  have := hP.prob
  rw [stateMarg_univ_eq_union M gam π P hP]
  exact prob_le_one

theorem iUnion_inInt_mono {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    (⋃ n, {ω : Traj X | inInt ω n s}) ⊆ ⋃ n, {ω : Traj X | inInt ω n t} := by
  intro ω hω
  simp only [mem_iUnion, mem_ofPred_eq] at hω ⊢
  obtain ⟨n, hn⟩ := hω
  have hex : ∃ k, ENNReal.ofReal t ≤ tn ω (k + 1) :=
    ⟨n, le_trans (ENNReal.ofReal_le_ofReal hts) hn.2⟩
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h0 | hs
  · rw [h0]; simp [tn, ht]
  · rw [hs]
    have := Nat.find_min hex (show Nat.pred (Nat.find hex) < Nat.find hex by omega)
    simpa using this

theorem stateMarg_univ_anti (M : Model X A) (gam : Measure X) (π : Policy X A)
    (P : Measure (Traj X)) (hP : IsLaw M gam π P) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    stateMarg P s univ ≤ stateMarg P t univ := by
  rw [stateMarg_univ_eq_union M gam π P hP s, stateMarg_univ]
  exact le_trans (measure_mono (iUnion_inInt_mono ht hts)) (measure_iUnion_le _)


theorem measurable_phi_at {M : Model X A} {phi : X → ℝ → Measure A} (hphi : IsMarkovPolicy M phi)
    {t : ℝ} (ht : 0 < t) {B : Set A} (hB : MeasurableSet B) : Measurable (fun z => phi z t B) := by
  have := hphi.measurable B hB
  exact this.comp (f := fun z => ((z, ⟨t, ht⟩) : X × Ioi (0:ℝ))) (by fun_prop)

theorem saMarg_markov {M : Model X A} {phi : X → ℝ → Measure A} (hphi : IsMarkovPolicy M phi)
    (P : Measure (Traj X)) {t : ℝ} (ht : 0 < t) {Z : Set X} (hZ : MeasurableSet Z)
    {B : Set A} (hB : MeasurableSet B) :
    saMarg P (markovPol phi) t Z B = ∫⁻ z in Z, phi z t B ∂(stateMarg P t) := by
  have hg : Measurable (fun z => phi z t B) := measurable_phi_at hphi ht hB
  unfold saMarg expAt stateMarg
  rw [← lintegral_indicator hZ, lintegral_sum_measure]
  congr 1; funext n
  rw [lintegral_map (hg.indicator hZ) (measurable_xn n)]
  congr 1; funext ω
  simp only [markovPol, add_sub_cancel]
  by_cases h : xn ω n ∈ Z <;> simp [h]

theorem saMarg_split_le {π : Policy X A}
    (hprob : ∀ n ω s, 0 < s → IsProbabilityMeasure (π n ω s))
    (P : Measure (Traj X)) (t : ℝ) {Z : Set X} (hZ : MeasurableSet Z)
    {B : Set A} (hB : MeasurableSet B) :
    saMarg P π t Z B + saMarg P π t Z Bᶜ + saMarg P π t Zᶜ univ ≤ stateMarg P t univ := by
  rw [stateMarg_univ]
  unfold saMarg expAt
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum (fun n => ?_)
  refine le_trans (add_le_add_left (le_lintegral_add _ _) _) ?_
  refine le_trans (le_lintegral_add _ _) ?_
  rw [← setLIntegral_one]
  refine setLIntegral_mono' (measurableSet_inInt n t) (fun ω hω => ?_)
  have hlt : (tn ω n).toReal < t := ENNReal.toReal_lt_of_lt_ofReal hω.1
  have := hprob n ω (t - (tn ω n).toReal) (by linarith)
  by_cases h : xn ω n ∈ Z
  · simp [h, prob_add_prob_compl hB]
  · simp [h]

theorem saMarg_markov_split {M : Model X A} {phi : X → ℝ → Measure A} (hphi : IsMarkovPolicy M phi)
    (P : Measure (Traj X)) {t : ℝ} (ht : 0 < t) {Z : Set X} (hZ : MeasurableSet Z)
    {B : Set A} (hB : MeasurableSet B) :
    saMarg P (markovPol phi) t Z B + saMarg P (markovPol phi) t Z Bᶜ +
      saMarg P (markovPol phi) t Zᶜ univ = stateMarg P t univ := by
  rw [saMarg_markov hphi P ht hZ hB, saMarg_markov hphi P ht hZ hB.compl,
    saMarg_markov hphi P ht hZ.compl MeasurableSet.univ,
    ← lintegral_add_left (measurable_phi_at hphi ht hB)]
  have e1 : ∫⁻ z in Z, (phi z t B + phi z t Bᶜ) ∂(stateMarg P t) = ∫⁻ z in Z, 1 ∂(stateMarg P t) := by
    congr 1; funext z
    have := hphi.prob z t ht
    exact prob_add_prob_compl hB
  have e2 : ∫⁻ z in Zᶜ, phi z t univ ∂(stateMarg P t) = ∫⁻ z in Zᶜ, 1 ∂(stateMarg P t) := by
    congr 1; funext z
    have := hphi.prob z t ht
    exact measure_univ
  rw [e1, e2, setLIntegral_one, setLIntegral_one, measure_add_measure_compl hZ]


theorem ext_mem_inl_inl (M : Model X A) (gam : Measure X) (x : X) (a : A) :
    (Sum.inl a : A ⊕ Bool) ∈ (extModel M gam).Aset (Sum.inl x) ↔ a ∈ M.Aset x := by
  simp [extModel, aDPrime]

theorem ext_mem_inl_inr (M : Model X A) (gam : Measure X) (x : X) (b : Bool) :
    (Sum.inr b : A ⊕ Bool) ∈ (extModel M gam).Aset (Sum.inl x) ↔ b = false := by
  simp [extModel, aDPrime]

theorem ext_mem_inr_inl (M : Model X A) (gam : Measure X) (u : Unit) (a : A) :
    (Sum.inl a : A ⊕ Bool) ∉ (extModel M gam).Aset (Sum.inr u) := by
  simp [extModel, aDPrime, aPrime]

theorem ext_mem_inr_inr (M : Model X A) (gam : Measure X) (u : Unit) (b : Bool) :
    (Sum.inr b : A ⊕ Bool) ∈ (extModel M gam).Aset (Sum.inr u) := by
  cases b <;> simp [extModel, aDPrime, aPrime]

theorem ext_aDPrime_mem (M : Model X A) (gam : Measure X) (z : X ⊕ Unit) :
    aDPrime ∈ (extModel M gam).Aset z := by
  rcases z with x | u
  · exact (ext_mem_inl_inr M gam x false).2 rfl
  · exact ext_mem_inr_inr M gam u false

theorem measurableSet_Aset {M : Model X A} (hM : M.Standing) (x : X) : MeasurableSet (M.Aset x) := by
  have := hM.graph_measurable
  exact measurable_prodMk_left this

theorem ext_jumpM_inl_inl (M : Model X A) (gam : Measure X) (x : X) (a : A) :
    (extModel M gam).jumpM (Sum.inl x) (Sum.inl a) = (M.jumpM x a).map Sum.inl := by
  unfold Model.jumpM
  rw [ext_mem_inl_inl]
  split_ifs <;> simp [extModel]

theorem ext_jumpM_inl_inr (M : Model X A) (gam : Measure X) (x : X) (b : Bool) :
    (extModel M gam).jumpM (Sum.inl x) (Sum.inr b) = 0 := by
  unfold Model.jumpM; split_ifs <;> simp [extModel]

theorem ext_jumpM_inr_inl (M : Model X A) (gam : Measure X) (u : Unit) (a : A) :
    (extModel M gam).jumpM (Sum.inr u) (Sum.inl a) = 0 := by
  unfold Model.jumpM; split_ifs <;> simp [extModel]

theorem ext_jumpM_inr_inr (M : Model X A) (gam : Measure X) (u : Unit) (b : Bool) :
    (extModel M gam).jumpM (Sum.inr u) (Sum.inr b) = if b then gam.map Sum.inl else 0 := by
  unfold Model.jumpM; rw [if_pos (ext_mem_inr_inr M gam u b)]; cases b <;> simp [extModel]

theorem ext_standing {M : Model X A} (hM : M.Standing) (gam : Measure X) [IsFiniteMeasure gam] :
    (extModel M gam).Standing where
  graph_measurable := by
    refine measurableSet_setOfPred.2 ?_
    refine meas_sum_prod _ (meas_prod_sum _ ?_ ?_) (meas_prod_sum _ ?_ ?_)
    · simp only [ext_mem_inl_inl]
      exact measurableSet_setOfPred.1 hM.graph_measurable
    · simp only [ext_mem_inl_inr]
      exact (measurable_of_countable (fun b : Bool => b = false)).comp measurable_snd
    · simp only [ext_mem_inr_inl]; exact measurable_const
    · simp only [ext_mem_inr_inr]; exact measurable_const
  selector := ⟨fun _ => aDPrime, measurable_const, ext_aDPrime_mem M gam⟩
  finite := by
    intro z a ha
    rcases z with x | u <;> rcases a with a | b
    · have : IsFiniteMeasure (M.qJ x a) := hM.finite x a ((ext_mem_inl_inl M gam x a).1 ha)
      simp only [extModel]; infer_instance
    · simp only [extModel]; infer_instance
    · simp only [extModel]; infer_instance
    · cases b <;> simp only [extModel] <;> infer_instance
  no_self := by
    intro z a ha
    rcases z with x | u <;> rcases a with a | b
    · have := hM.no_self x a ((ext_mem_inl_inl M gam x a).1 ha)
      simp only [extModel]
      rw [memb_inl.map_apply]
      have e : (Sum.inl ⁻¹' {(Sum.inl x : X ⊕ Unit)} : Set X) = {x} := by ext; simp
      rw [e]; exact this
    · simp [extModel]
    · simp [extModel]
    · cases b
      · simp [extModel]
      · simp only [extModel]
        rw [memb_inl.map_apply]
        have e : (Sum.inl ⁻¹' {Sum.inr u} : Set X) = ∅ := by ext; simp
        rw [e, measure_empty]
  measurable := by
    intro Z hZ
    refine meas_sum_prod _ (meas_prod_sum _ ?_ ?_) (meas_prod_sum _ ?_ ?_)
    · simp only [ext_jumpM_inl_inl]
      have := hM.measurable _ (measurable_inl hZ)
      have e : (fun p : X × A => ((M.jumpM p.1 p.2).map Sum.inl) Z) =
          fun p => M.jumpM p.1 p.2 (Sum.inl ⁻¹' Z) := by
        funext p; exact memb_inl.map_apply _ _
      rw [e]; exact this
    · simp only [ext_jumpM_inl_inr]; exact measurable_const
    · simp only [ext_jumpM_inr_inl]; exact measurable_const
    · exact measurable_of_countable _

theorem ext_A21 {M : Model X A} (hA : M.Assumption21) (gam : Measure X) [IsFiniteMeasure gam] :
    (extModel M gam).Assumption21 := by
  intro z
  rcases z with x | u
  · have hx := hA x
    refine lt_of_le_of_lt ?_ hx
    refine iSup₂_le (fun a ha => ?_)
    rcases a with a | b
    · have ha' := (ext_mem_inl_inl M gam x a).1 ha
      refine le_trans ?_ (le_iSup₂ (f := fun a _ => M.rate x a) a ha')
      simp only [Model.rate, ext_jumpM_inl_inl]
      rw [Measure.map_apply measurable_inl MeasurableSet.univ]; simp
    · simp [Model.rate, ext_jumpM_inl_inr]
  · refine lt_of_le_of_lt (iSup₂_le (fun a _ => (?_ : _ ≤ gam univ + 0))) (by simpa using measure_lt_top gam univ)
    rcases a with a | b
    · simp [Model.rate, ext_jumpM_inr_inl]
    · cases b
      · simp [Model.rate, ext_jumpM_inr_inr]
      · simp [Model.rate, ext_jumpM_inr_inr, memb_inl.map_apply]


section Ext

attribute [local instance] sb_sum

variable [StandardBorelSpace X] [StandardBorelSpace A]

theorem dirac_compl_zero {α : Type*} [MeasurableSpace α] {S : Set α} (hS : MeasurableSet S) {a : α}
    (ha : a ∈ S) : Measure.dirac a Sᶜ = 0 := by
  rw [Measure.dirac_apply' _ hS.compl]; simp [ha]

theorem ext_measurableSet_Aset {M : Model X A} (hM : M.Standing) (gam : Measure X) [IsFiniteMeasure gam]
    (z : X ⊕ Unit) : MeasurableSet ((extModel M gam).Aset z) :=
  measurableSet_Aset (ext_standing hM gam) z

theorem ext_preimage_compl (M : Model X A) (gam : Measure X) (x : X) :
    (Sum.inl ⁻¹' ((extModel M gam).Aset (Sum.inl x))ᶜ : Set A) = (M.Aset x)ᶜ := by
  ext a; simp [ext_mem_inl_inl]

theorem extMarkov_isMarkov {M : Model X A} (hM : M.Standing) (gam : Measure X) [IsFiniteMeasure gam]
    {phi : X → ℝ → Measure A} (hphi : IsMarkovPolicy M phi) {u : ℝ} (hu : 0 < u) :
    IsMarkovPolicy (extModel M gam) (extMarkov phi u) where
  prob := by
    intro z t ht
    rcases z with x | v
    · simp only [extMarkov]
      split_ifs with h
      · infer_instance
      · have := hphi.prob x (t - u) (by linarith [not_le.1 h])
        exact Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
    · simp only [extMarkov]; split_ifs <;> infer_instance
  feasible := by
    intro z t ht
    rcases z with x | v
    · simp only [extMarkov]
      split_ifs with h
      · exact dirac_compl_zero (ext_measurableSet_Aset hM gam _) (ext_aDPrime_mem M gam _)
      · rw [Measure.map_apply measurable_inl (ext_measurableSet_Aset hM gam _).compl,
          ext_preimage_compl]
        exact hphi.feasible x (t - u) (by linarith [not_le.1 h])
    · simp only [extMarkov]
      split_ifs with h
      · exact dirac_compl_zero (ext_measurableSet_Aset hM gam _) (ext_mem_inr_inr M gam v true)
      · exact dirac_compl_zero (ext_measurableSet_Aset hM gam _) (ext_mem_inr_inr M gam v false)
  measurable := by
    intro B hB
    refine meas_sum_prod _ ?_ ?_
    · let g : X × Ioi (0:ℝ) → ℝ≥0∞ := fun p =>
        phi p.1 (if u < (p.2 : ℝ) then (p.2 : ℝ) - u else 1) (Sum.inl ⁻¹' B)
      have hg : Measurable g := by
        have := hphi.measurable _ (measurable_inl hB)
        refine this.comp (f := fun p : X × Ioi (0:ℝ) =>
          ((p.1, ⟨if u < (p.2 : ℝ) then (p.2 : ℝ) - u else 1, by
            split_ifs with h
            · simp only [mem_Ioi]; linarith
            · simp⟩) : X × Ioi (0:ℝ))) ?_
        refine measurable_fst.prodMk (Measurable.subtype_mk ?_)
        refine Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop) measurable_const
      have e : (fun p : X × Ioi (0:ℝ) => extMarkov phi u (Sum.inl p.1) p.2 B) =
          fun p => if (p.2 : ℝ) ≤ u then Measure.dirac aDPrime B else g p := by
        funext p
        simp only [extMarkov, g]
        split_ifs with h1 h2
        · rfl
        · rw [Measure.map_apply measurable_inl hB]
        · exact absurd (not_le.1 h1) h2
      rw [e]
      exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const hg
    · have e : (fun p : Unit × Ioi (0:ℝ) => extMarkov phi u (Sum.inr p.1) p.2 B) =
          fun p => if (p.2 : ℝ) ≤ u then Measure.dirac aPrime B else Measure.dirac aDPrime B := by
        funext p
        simp only [extMarkov]
        split_ifs <;> rfl
      rw [e]
      exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const
        measurable_const

theorem measurable_projX [Nonempty X] : Measurable (projX (X := X)) :=
  measurable_id.sumElim measurable_const

theorem measurable_shiftTraj [Nonempty X] (u : ℝ) : Measurable (shiftTraj (X := X) u) := by
  unfold shiftTraj
  refine (measurable_projX.comp (measurable_xn 1)).prodMk (measurable_pi_lambda _ fun k => ?_)
  exact ((measurable_tn (k+2)).sub measurable_const).prodMk (measurable_projX.comp (measurable_xn (k+2)))

theorem xn_shift_pred [Nonempty X] (u : ℝ) (ω : Traj (X ⊕ Unit)) {n : ℕ} (hn : 1 ≤ n) :
    xn (shiftTraj u ω) (n - 1) = projX (xn ω n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  cases k with
  | zero => rfl
  | succ j => rfl

theorem arg_pos [Nonempty X] {u : ℝ} (hu : 0 < u) (ω : Traj (X ⊕ Unit)) {n : ℕ} {s : ℝ}
    (hs : 0 < s) (hns : ¬ (tn ω n).toReal + s ≤ u) (hn : 1 ≤ n) (hO : inOmegaU u n ω) :
    0 < (tn ω n).toReal + s - u - (tn (shiftTraj u ω) (n - 1)).toReal := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  cases k with
  | zero =>
    simp only [Nat.add_sub_cancel, tn, ENNReal.toReal_zero]
    simp only [tn] at hns
    linarith
  | succ j =>
    have hlt : ENNReal.ofReal u < tn ω (j + 2) := hO.2.2.2.2 (j + 2) (by omega) le_rfl
    have e : tn (shiftTraj u ω) (j + 1 + 1 - 1) = tn ω (j + 2) - ENNReal.ofReal u := rfl
    rw [e]
    by_cases htop : tn ω (j + 2) = ⊤
    · have : tn ω (j + 1 + 1) = ⊤ := htop
      have h2 : (⊤ : ℝ≥0∞) - ENNReal.ofReal u = ⊤ := by simp
      rw [this] at hns ⊢
      rw [h2]; simp only [ENNReal.toReal_top] at hns ⊢
      linarith
    · have : tn ω (j + 1 + 1) = tn ω (j + 2) := rfl
      rw [this, ENNReal.toReal_sub_of_le hlt.le htop, ENNReal.toReal_ofReal hu.le]
      linarith

theorem extPol_isPolicy {M : Model X A} (hM : M.Standing) (gam : Measure X) [IsFiniteMeasure gam]
    [Nonempty X] {σ : Policy X A} (hσ : IsPolicy M σ) {u : ℝ} (hu : 0 < u) :
    IsPolicy (extModel M gam) (extPol σ u) where
  prob := by
    intro n ω s hs
    unfold extPol
    split_ifs with h1 h2 h3 h4
    · infer_instance
    · infer_instance
    · infer_instance
    · have := hσ.prob (n - 1) (shiftTraj u ω) _ (arg_pos hu ω hs h1 h4.1 h4.2)
      exact Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
    · infer_instance
  feasible := by
    intro n ω s hs
    unfold extPol
    split_ifs with h1 h2 h3 h4
    · rw [h2]; exact dirac_compl_zero (ext_measurableSet_Aset hM gam _) (ext_mem_inr_inr M gam () true)
    · exact dirac_compl_zero (ext_measurableSet_Aset hM gam _) (ext_aDPrime_mem M gam _)
    · exact dirac_compl_zero (ext_measurableSet_Aset hM gam _) (ext_aDPrime_mem M gam _)
    · obtain ⟨y, hy⟩ := h4.2.2.2.2.1 n h4.1 le_rfl
      rw [Measure.map_apply measurable_inl (ext_measurableSet_Aset hM gam _).compl, hy,
        ext_preimage_compl]
      have := hσ.feasible (n - 1) (shiftTraj u ω) _ (arg_pos hu ω hs h1 h4.1 h4.2)
      rwa [xn_shift_pred u ω h4.1, hy] at this
    · exact dirac_compl_zero (ext_measurableSet_Aset hM gam _) (ext_aDPrime_mem M gam _)
  nonanticipating := by
    intro n ω ω' h
    have htn := (h n le_rfl).1
    have hxn := (h n le_rfl).2
    cases n with
    | zero =>
      funext s
      have : ¬ (1 ≤ 0) := by omega
      simp only [extPol, this, false_and, if_false]
      rw [htn, hxn]
    | succ k =>
      have hO : inOmegaU u (k + 1) ω ↔ inOmegaU u (k + 1) ω' := by
        unfold inOmegaU
        have h0 : ω.1 = ω'.1 := (h 0 (Nat.zero_le _)).2
        have h1 : tn ω 1 = tn ω' 1 := (h 1 (by omega)).1
        rw [h0, h1]
        refine and_congr_right' (and_congr_right' (and_congr_right' (and_congr ?_ ?_)))
        · refine forall_congr' fun j => imp_congr_right fun _ => imp_congr_right fun hj => ?_
          rw [(h j hj).2]
        · refine forall_congr' fun j => imp_congr_right fun _ => imp_congr_right fun hj => ?_
          rw [(h j hj).1]
      have hsh : ∀ j ≤ k, tn (shiftTraj u ω) j = tn (shiftTraj u ω') j ∧
          xn (shiftTraj u ω) j = xn (shiftTraj u ω') j := by
        intro j hj
        cases j with
        | zero =>
          refine ⟨rfl, ?_⟩
          show projX (xn ω 1) = projX (xn ω' 1)
          rw [(h 1 (by omega)).2]
        | succ i =>
          refine ⟨?_, ?_⟩
          · show tn ω (i + 2) - ENNReal.ofReal u = tn ω' (i + 2) - ENNReal.ofReal u
            rw [(h (i + 2) (by omega)).1]
          · show projX (xn ω (i + 2)) = projX (xn ω' (i + 2))
            rw [(h (i + 2) (by omega)).2]
      have hσe := hσ.nonanticipating k _ _ hsh
      have htk := (hsh k le_rfl).1
      funext s
      simp only [extPol, Nat.add_sub_cancel]
      rw [htn, hxn, hσe, htk, show inOmegaU u (k+1) ω = inOmegaU u (k+1) ω' from propext hO]
  measurable := by
    classical
    intro n B hB
    let arg : Traj (X ⊕ Unit) × Ioi (0:ℝ) → ℝ := fun p =>
      (tn p.1 n).toReal + p.2 - u - (tn (shiftTraj u p.1) (n - 1)).toReal
    have harg : Measurable arg := by
      have h1 : Measurable (fun p : Traj (X ⊕ Unit) × Ioi (0:ℝ) => (tn p.1 n).toReal) :=
        ENNReal.measurable_toReal.comp ((measurable_tn n).comp measurable_fst)
      have h2 : Measurable (fun p : Traj (X ⊕ Unit) × Ioi (0:ℝ) => (tn (shiftTraj u p.1) (n - 1)).toReal) :=
        ENNReal.measurable_toReal.comp (((measurable_tn (n-1)).comp (measurable_shiftTraj u)).comp measurable_fst)
      exact ((h1.add (measurable_subtype_coe.comp measurable_snd)).sub measurable_const).sub h2
    let g : Traj (X ⊕ Unit) × Ioi (0:ℝ) → ℝ≥0∞ := fun p =>
      σ (n - 1) (shiftTraj u p.1) (if 0 < arg p then arg p else 1) (Sum.inl ⁻¹' B)
    have hg : Measurable g := by
      have := hσ.measurable (n - 1) _ (measurable_inl hB)
      refine this.comp (f := fun p : Traj (X ⊕ Unit) × Ioi (0:ℝ) =>
        ((shiftTraj u p.1, ⟨if 0 < arg p then arg p else 1, by
          split_ifs with h
          · exact h
          · simp⟩) : Traj X × Ioi (0:ℝ))) ?_
      refine ((measurable_shiftTraj u).comp measurable_fst).prodMk (Measurable.subtype_mk ?_)
      exact Measurable.ite (measurableSet_lt measurable_const harg) harg measurable_const
    have hc1 : MeasurableSet {p : Traj (X ⊕ Unit) × Ioi (0:ℝ) | (tn p.1 n).toReal + p.2 ≤ u} :=
      measurableSet_le ((ENNReal.measurable_toReal.comp ((measurable_tn n).comp measurable_fst)).add
        (measurable_subtype_coe.comp measurable_snd)) measurable_const
    have hc2 : MeasurableSet {p : Traj (X ⊕ Unit) × Ioi (0:ℝ) | xn p.1 n = xPrime} :=
      ((measurable_xn n).comp measurable_fst) (measurableSet_singleton _)
    have hO : Measurable (fun ω : Traj (X ⊕ Unit) => inOmegaU u n ω) := by
      unfold inOmegaU
      refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_)))
      · exact measurableSet_setOfPred.1 (measurable_fst (measurableSet_singleton _))
      · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const (measurable_tn 1))
      · exact measurableSet_setOfPred.1 (measurableSet_le (measurable_tn 1) measurable_const)
      · refine Measurable.forall fun j => Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
        have e : {ω : Traj (X ⊕ Unit) | ∃ y, xn ω j = Sum.inl y} = (fun ω => xn ω j) ⁻¹' range Sum.inl := by
          ext ω; simp [eq_comm]
        exact measurableSet_setOfPred.1 (e ▸ (measurable_xn j) measurableSet_range_inl)
      · refine Measurable.forall fun j => Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
        exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const (measurable_tn j))
    have hc3 : MeasurableSet {p : Traj (X ⊕ Unit) × Ioi (0:ℝ) | 1 ≤ n ∧ inOmegaU u n p.1} :=
      measurableSet_setOfPred.2 (measurable_const.and (hO.comp measurable_fst))
    have e : (fun p : Traj (X ⊕ Unit) × Ioi (0:ℝ) => extPol σ u n p.1 p.2 B) =
        fun p => if (tn p.1 n).toReal + p.2 ≤ u then
          (if xn p.1 n = xPrime then Measure.dirac aPrime B else Measure.dirac aDPrime B)
        else if xn p.1 n = xPrime then Measure.dirac aDPrime B
        else if 1 ≤ n ∧ inOmegaU u n p.1 then g p else Measure.dirac aDPrime B := by
      funext p
      simp only [extPol]
      split_ifs with h1 h2 h3 h4
      · rfl
      · rfl
      · rfl
      · simp only [g, arg]
        rw [if_pos (arg_pos hu p.1 p.2.2 h1 h4.1 h4.2), Measure.map_apply measurable_inl hB]
      · rfl
    rw [e]
    refine Measurable.ite hc1 (Measurable.ite hc2 measurable_const measurable_const)
      (Measurable.ite hc2 measurable_const (Measurable.ite hc3 hg measurable_const))

end Ext

theorem markovPol_isPolicy {M : Model X A} {phi : X → ℝ → Measure A} (hphi : IsMarkovPolicy M phi) :
    IsPolicy M (markovPol phi) where
  prob := fun n ω s hs => hphi.prob _ _ (by have := ENNReal.toReal_nonneg (a := tn ω n); linarith)
  feasible := fun n ω s hs => hphi.feasible _ _ (by have := ENNReal.toReal_nonneg (a := tn ω n); linarith)
  nonanticipating := by
    intro n ω ω' h
    funext s
    simp only [markovPol, (h n le_rfl).1, (h n le_rfl).2]
  measurable := by
    intro n B hB
    have := hphi.measurable B hB
    refine this.comp (f := fun p : Traj X × Ioi (0:ℝ) =>
      ((xn p.1 n, ⟨(tn p.1 n).toReal + p.2, by
        have := ENNReal.toReal_nonneg (a := tn p.1 n); have := p.2.2
        simp only [mem_Ioi] at this ⊢; linarith⟩) : X × Ioi (0:ℝ))) ?_
    exact ((measurable_xn n).comp measurable_fst).prodMk (Measurable.subtype_mk
      ((ENNReal.measurable_toReal.comp ((measurable_tn n).comp measurable_fst)).add
        (measurable_subtype_coe.comp measurable_snd)))

end CTJMDPAux

open CTJMDPAux

theorem solution {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (gam : Measure X) [IsProbabilityMeasure gam]
    (π : Policy X A) (hπ : IsPolicy M π)
    (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (Ppi Pphi : Measure (Traj X)) (hPpi : IsLaw M gam π Ppi)
    (hPphi : IsLaw M gam (markovPol phi) Pphi)
    (h16 : Disintegrates Ppi π phi) :
    (∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
      saMarg Pphi (markovPol phi) t Z B ≤ saMarg Ppi π t Z B) ∧
    (∀ s : ℝ, 0 < s → stateMarg Pphi s univ = 1 →
      ∀ t ∈ Ioc (0 : ℝ) s, ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
        saMarg Pphi (markovPol phi) t Z B = saMarg Ppi π t Z B) ∧
    ((∀ t : ℝ, 0 < t → stateMarg Pphi t univ = 1) →
      ∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
        saMarg Pphi (markovPol phi) t Z B = saMarg Ppi π t Z B) := by
  have hX : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := gam)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact zero_ne_one h1
  -- Step 1: inequality (20), via the extended model of p. 15–16 with `u = 1`.
  have hineq : ∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
      saMarg Pphi (markovPol phi) t Z B ≤ saMarg Ppi π t Z B := by
    intro t ht Z B hZ hB
    have : StandardBorelSpace (X ⊕ Unit) := sb_sum
    have : StandardBorelSpace (A ⊕ Bool) := sb_sum
    have hu : (0 : ℝ) < 1 := one_pos
    have hM' := ext_standing hM gam
    have hA' := ext_A21 hA gam
    have hπ' := extPol_isPolicy hM gam hπ hu
    have hphi' := extMarkov_isMarkov hM gam hphi hu
    obtain ⟨Ptpi, hPtpi⟩ := (law_exists_unique (extModel M gam) hM' hA'
      (Measure.dirac xPrime) (extPol π 1) hπ').exists
    obtain ⟨Ptphi, hPtphi⟩ := (law_exists_unique (extModel M gam) hM' hA'
      (Measure.dirac xPrime) (markovPol (extMarkov phi 1)) (markovPol_isPolicy hphi')).exists
    have h16' := ext_disintegrates M hM hA gam 1 hu π hπ Ppi hPpi phi hphi h16 Ptpi hPtpi
    have h5 := (lemma_5 (extModel M gam) hM' hA' xPrime (extPol π 1) hπ' (extMarkov phi 1) hphi'
      Ptpi Ptphi hPtpi hPtphi h16').1 (t + 1) (by linarith) (Sum.inl '' Z) (Sum.inl '' B)
      (memb_inl.measurableSet_image' hZ) (memb_inl.measurableSet_image' hB)
    have e1 := (eq_58_59 M hM hA gam 1 hu).1 π hπ Ppi Ptpi hPpi hPtpi t ht Z B hZ hB
    have e2 := (eq_58_59 M hM hA gam 1 hu).2 phi hphi Pphi Ptphi hPphi hPtphi t ht Z B hZ hB
    rw [e1, e2] at h5
    have hc0 : ENNReal.ofReal (1 - Real.exp (-1)) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le, sub_pos]
      exact Real.exp_lt_one_iff.2 (by norm_num)
    exact (ENNReal.mul_le_mul_iff_right hc0 ENNReal.ofReal_ne_top).1 h5
  -- Step 2: equality on `]0, s]` when `P^ϕ_γ(s, X) = 1` (last paragraph of the proof, p. 17).
  have heq : ∀ s : ℝ, 0 < s → stateMarg Pphi s univ = 1 →
      ∀ t ∈ Ioc (0 : ℝ) s, ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
        saMarg Pphi (markovPol phi) t Z B = saMarg Ppi π t Z B := by
    intro s hs hs1 t ht Z B hZ hB
    have ht0 : 0 < t := ht.1
    have hφ1 : 1 ≤ stateMarg Pphi t univ :=
      hs1 ▸ stateMarg_univ_anti M gam (markovPol phi) Pphi hPphi ht0 ht.2
    have hφle := stateMarg_univ_le_one M gam (markovPol phi) Pphi hPphi t
    have hsφ := saMarg_markov_split hphi Pphi ht0 hZ hB
    have hsπ := saMarg_split_le hπ.prob Ppi t hZ hB
    have hπ1 := stateMarg_univ_le_one M gam π Ppi hPpi t
    have ha := hineq t ht0 Z B hZ hB
    have hb := hineq t ht0 Z Bᶜ hZ hB.compl
    have hc := hineq t ht0 Zᶜ univ hZ.compl MeasurableSet.univ
    rw [add_assoc] at hsφ hsπ
    have hfin : saMarg Pphi (markovPol phi) t Z Bᶜ + saMarg Pphi (markovPol phi) t Zᶜ univ ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      rw [← hsφ] at hφle
      exact le_trans le_add_self hφle
    refine le_antisymm ha (ENNReal.le_of_add_le_add_right hfin ?_)
    calc saMarg Ppi π t Z B + (saMarg Pphi (markovPol phi) t Z Bᶜ +
          saMarg Pphi (markovPol phi) t Zᶜ univ)
        ≤ saMarg Ppi π t Z B + (saMarg Ppi π t Z Bᶜ + saMarg Ppi π t Zᶜ univ) :=
          add_le_add le_rfl (add_le_add hb hc)
      _ ≤ 1 := le_trans hsπ hπ1
      _ ≤ _ := by rw [hsφ]; exact hφ1
  refine ⟨hineq, heq, ?_⟩
  intro hall t ht Z B hZ hB
  exact heq t ht (hall t ht) t ⟨ht, le_rfl⟩ Z B hZ hB
