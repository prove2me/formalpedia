-- Prove2me | solution 1 for CTJMDP.MarkovSuff.lemma_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:45:23.239492+00:00
-- url     : https://prove2.me/submissions/137225db-6c96-42a3-9a43-f4d8abc4a606
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting
import Theorems.Thm_CTJMDP_MarkovSuff_corollary_5
import Theorems.Thm_CTJMDP_MarkovSuff_lemma_4
import Theorems.Thm_CTJMDP_MarkovSuff_eq_49_50

open CTJMDP.MarkovSuff MeasureTheory Set
open scoped ENNReal

namespace CTJMDPAuxL2

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

theorem stateMarg_apply (P : Measure (Traj X)) (t : ℝ) {Z : Set X} (hZ : MeasurableSet Z) :
    stateMarg P t Z = ∑' n, P {ω | inInt ω n t ∧ xn ω n ∈ Z} := by
  unfold stateMarg
  rw [Measure.sum_apply _ hZ]
  congr 1; funext n
  rw [Measure.map_apply (measurable_xn n) hZ, Measure.restrict_apply ((measurable_xn n) hZ)]
  congr 1; ext ω; simp [and_comm]

theorem measurable_stateMarg (P : Measure (Traj X)) [SFinite P] {Z : Set X} (hZ : MeasurableSet Z) :
    Measurable (fun t : Ioi (0 : ℝ) => stateMarg P t Z) := by
  simp_rw [stateMarg_apply P _ hZ]
  refine Measurable.ennreal_tsum fun n => ?_
  have hS : MeasurableSet {q : Traj X × ℝ | inInt q.1 n q.2 ∧ xn q.1 n ∈ Z} := by
    unfold inInt
    refine ((measurableSet_lt ((measurable_tn n).comp measurable_fst)
      (ENNReal.measurable_ofReal.comp measurable_snd)).inter
      (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd)
        ((measurable_tn (n+1)).comp measurable_fst))).inter ?_
    exact ((measurable_xn n).comp measurable_fst) hZ
  exact (measurable_measure_prodMk_right (μ := P) hS).comp measurable_subtype_coe

/-- `ν(z, a, {z}) = 0` for the extended-by-zero jump measure. -/
theorem jumpM_singleton {M : Model X A} (hM : M.Standing) (z : X) (a : A) :
    M.jumpM z a {z} = 0 := by
  unfold Model.jumpM
  split_ifs with h
  · exact hM.no_self z a h
  · simp

theorem measurable_jumpM_kernel {M : Model X A} (hM : M.Standing) (z : X) :
    Measurable (fun a => M.jumpM z a) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  exact (hM.measurable S hS).comp (measurable_prodMk_left (x := z))

theorem jumpP_apply {M : Model X A} (hM : M.Standing) (z : X) (p : Measure A) {S : Set X}
    (hS : MeasurableSet S) : jumpP M z p S = ∫⁻ a, M.jumpM z a S ∂p := by
  unfold jumpP
  exact Measure.bind_apply hS (measurable_jumpM_kernel hM z).aemeasurable

theorem jumpP_compl {M : Model X A} [MeasurableSingletonClass X] (hM : M.Standing) (z : X)
    (p : Measure A) : jumpP M z p {z}ᶜ = rateP M z p := by
  rw [jumpP_apply hM z p (measurableSet_singleton z).compl]
  unfold rateP Model.rate
  congr 1; funext a
  have := measure_add_measure_compl (μ := M.jumpM z a) (measurableSet_singleton z)
  rwa [jumpM_singleton hM, zero_add] at this

theorem jumpP_diff {M : Model X A} [MeasurableSingletonClass X] (hM : M.Standing) (z : X)
    (p : Measure A) {Z : Set X} (hZ : MeasurableSet Z) :
    jumpP M z p (Z \ {z}) = ∫⁻ a, M.jumpM z a Z ∂p := by
  rw [jumpP_apply hM z p (hZ.diff (measurableSet_singleton z))]
  congr 1; funext a
  exact measure_sdiff_null (jumpM_singleton hM z a)

end CTJMDPAuxL2

open CTJMDPAuxL2

theorem solution {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (π : Policy X A) (hπ : IsPolicy M π)
    (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (Ppi Pphi : Measure (Traj X)) (hPpi : IsLaw M (Measure.dirac x) π Ppi)
    (hPphi : IsLaw M (Measure.dirac x) (markovPol phi) Pphi)
    (h16 : Disintegrates Ppi π phi) :
    (IsFwdSol M phi x (stateMarg Ppi) ∧ IsFwdSol M phi x (stateMarg Pphi)) ∧
    (∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z → stateMarg Pphi t Z ≤ stateMarg Ppi t Z) ∧
    (∀ s : ℝ, 0 < s → stateMarg Pphi s univ = 1 →
      ∀ t ∈ Ioc (0 : ℝ) s, ∀ Z : Set X, MeasurableSet Z → stateMarg Pphi t Z = stateMarg Ppi t Z) ∧
    ((∀ t : ℝ, 0 < t → stateMarg Pphi t univ = 1) →
      ∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z →
        stateMarg Pphi t Z = stateMarg Ppi t Z) := by
  obtain ⟨c1, c2, c3, c4⟩ := corollary_5 M hM hA x phi hphi Pphi hPphi
  have hle1 : ∀ t : ℝ, 0 < t → stateMarg Ppi t univ ≤ 1 :=
    fun t _ => stateMarg_univ_le_one M _ π Ppi hPpi t
  have hprob := hPpi.prob
  -- Statement (i) for `P^π_x`: it solves the forward equation (32) for `ϕ`.
  have hsol : IsFwdSol M phi x (stateMarg Ppi) := by
    refine ⟨fun t ht => lt_of_le_of_lt (hle1 t ht) ENNReal.one_lt_top,
      fun Z hZ => measurable_stateMarg Ppi hZ, ?_⟩
    intro t ht Z hYZ
    obtain ⟨hZ, C, hC, hCb⟩ := hYZ
    have hrate : Measurable (Function.uncurry fun z a => M.rate z a) := hM.measurable univ MeasurableSet.univ
    have hjZ : Measurable (Function.uncurry fun z a => M.jumpM z a Z) := hM.measurable Z hZ
    -- (49) with `f = q̃`: `𝔼 q̃(ξ_s, π_s) I{ξ_s ∈ Z} = ∫_Z q(z, s) P^π_x(s, dz)`
    have h49 : ∀ s : ℝ, 0 < s → outRate M Ppi π s Z =
        ∫⁻ z in Z, qOf M phi z s {z}ᶜ ∂(stateMarg Ppi s) := by
      intro s hs
      have := (eq_49_50 M hM hA x π hπ phi hphi Ppi hPpi h16 (fun z a => M.rate z a) hrate Z hZ).1 s hs
      unfold outRate
      rw [show (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * rateP M z p) =
        (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, M.rate z a ∂p) from rfl, this]
      congr 1; funext z
      rw [qOf, jumpP_compl hM]; rfl
    -- every `Z ∈ 𝒴^ϕ` is `(x, π)`-bounded
    have hbdd : IsBoundedFor M Ppi π Z := by
      refine lt_of_le_of_lt ?_ hC
      refine iSup₂_le fun s hs => ?_
      rw [h49 s hs]
      calc ∫⁻ z in Z, qOf M phi z s {z}ᶜ ∂(stateMarg Ppi s)
          ≤ ∫⁻ _ in Z, C ∂(stateMarg Ppi s) := setLIntegral_mono' hZ fun z hz => hCb z hz s hs
        _ = C * stateMarg Ppi s Z := by rw [setLIntegral_const]
        _ ≤ C * 1 := by
          gcongr
          exact le_trans (measure_mono (subset_univ Z)) (hle1 s hs)
        _ = C := mul_one C
    obtain ⟨hfin, heqn⟩ := lemma_4 M hM hA x π hπ Ppi hPpi Z hZ hbdd t ht
    -- (50) for the two integrals in (37)
    have h50a : EnuTilde M Ppi π t Z =
        ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z in Z, qOf M phi z s {z}ᶜ ∂(stateMarg Ppi s) := by
      have := (eq_49_50 M hM hA x π hπ phi hphi Ppi hPpi h16 (fun z a => M.rate z a) hrate Z hZ).2 t ht
      unfold EnuTilde EnuTildeAt
      rw [show expPathAt Ppi π (fun _ => t)
          (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * rateP M z p) =
        expPath Ppi π t (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, M.rate z a ∂p)
        from rfl, this.1, this.2]
      congr 1; funext s; congr 1; funext z
      rw [qOf, jumpP_compl hM]; rfl
    have h50b : EnuPi M Ppi π t Z =
        ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z, qOf M phi z s (Z \ {z}) ∂(stateMarg Ppi s) := by
      have := (eq_49_50 M hM hA x π hπ phi hphi Ppi hPpi h16 (fun z a => M.jumpM z a Z) hjZ univ
        MeasurableSet.univ).2 t ht
      unfold EnuPi EnuPiAt
      rw [show (fun z p => jumpP M z p (Z \ {z})) =
          (fun z p => (univ : Set X).indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, M.jumpM z a Z ∂p) by
        funext z p; rw [jumpP_diff hM z p hZ]; simp]
      rw [show expPathAt Ppi π (fun _ => t)
          (fun z p => (univ : Set X).indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, M.jumpM z a Z ∂p) =
        expPath Ppi π t (fun z p => (univ : Set X).indicator (fun _ => (1 : ℝ≥0∞)) z *
          ∫⁻ a, M.jumpM z a Z ∂p) from rfl, this.1, this.2]
      congr 1; funext s
      rw [Measure.restrict_univ]
      congr 1; funext z
      rw [qOf, jumpP_diff hM z _ hZ]
    refine ⟨lt_of_le_of_lt (le_trans (measure_mono (subset_univ Z)) (hle1 t ht)) ENNReal.one_lt_top,
      h50a ▸ hfin, ?_⟩
    rw [← h50a, ← h50b]
    exact heqn
  refine ⟨⟨hsol, c1⟩, ?_, ?_, ?_⟩
  · exact fun t ht Z hZ => c2 (stateMarg Ppi) hsol t ht Z hZ
  · exact fun s hs hs1 t ht Z hZ => (c3 s hs hs1 (stateMarg Ppi) hsol hle1 t ht Z hZ).symm
  · exact fun hall t ht Z hZ => (c4 hall (stateMarg Ppi) hsol hle1 t ht Z hZ).symm
