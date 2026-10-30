-- Prove2me | solution 1 for CTJMDP.MarkovSuff.eq_49_50
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:51:07.343777+00:00
-- url     : https://prove2.me/submissions/f066f678-37bd-42bb-9c7f-836c75d25d1d

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

open CTJMDP.MarkovSuff MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace CTJMDPAuxE49

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

theorem measurable_phi_at {M : Model X A} {phi : X → ℝ → Measure A} (hphi : IsMarkovPolicy M phi)
    {t : ℝ} (ht : 0 < t) {B : Set A} (hB : MeasurableSet B) : Measurable (fun z => phi z t B) := by
  have := hphi.measurable B hB
  exact this.comp (f := fun z => ((z, ⟨t, ht⟩) : X × Ioi (0:ℝ))) (by fun_prop)

theorem measurable_pol {M : Model X A} {π : Policy X A} (hπ : IsPolicy M π) (n : ℕ) :
    Measurable (fun p : Traj X × Ioi (0:ℝ) => π n p.1 p.2) :=
  Measure.measurable_of_measurable_coe _ (fun B hB => hπ.measurable n B hB)

/-- The time since the `n`th jump, clamped to be positive. -/
noncomputable def clampT (n : ℕ) (q : Traj X × ℝ) : Ioi (0:ℝ) :=
  ⟨if 0 < q.2 - (tn q.1 n).toReal then q.2 - (tn q.1 n).toReal else 1, by
    split_ifs with h
    · exact h
    · simp⟩

theorem measurable_clampT (n : ℕ) : Measurable (clampT (X := X) n) := by
  unfold clampT
  refine Measurable.subtype_mk ?_
  have hm : Measurable (fun q : Traj X × ℝ => q.2 - (tn q.1 n).toReal) :=
    measurable_snd.sub (ENNReal.measurable_toReal.comp ((measurable_tn n).comp measurable_fst))
  exact Measurable.ite (measurableSet_lt measurable_const hm) hm measurable_const

theorem clampT_eq {n : ℕ} {ω : Traj X} {s : ℝ} (h : inInt ω n s) :
    ((clampT n (ω, s) : Ioi (0:ℝ)) : ℝ) = s - (tn ω n).toReal := by
  have hlt : (tn ω n).toReal < s := ENNReal.toReal_lt_of_lt_ofReal h.1
  simp only [clampT]
  rw [if_pos (by linarith)]

/-- The action kernel `(ω, s) ↦ π_n(· | ω, s − t_n)` (time clamped). -/
noncomputable def polKer {M : Model X A} {π : Policy X A} (hπ : IsPolicy M π) (n : ℕ) :
    Kernel (Traj X × ℝ) A :=
  ⟨fun q => π n q.1 (clampT n q),
    (measurable_pol hπ n).comp (measurable_fst.prodMk (measurable_clampT n))⟩

instance {M : Model X A} {π : Policy X A} (hπ : IsPolicy M π) (n : ℕ) :
    IsMarkovKernel (polKer hπ n) :=
  ⟨fun q => hπ.prob n q.1 _ (clampT n q).2⟩

theorem polKer_apply {M : Model X A} {π : Policy X A} (hπ : IsPolicy M π) (n : ℕ) (q : Traj X × ℝ) :
    polKer hπ n q = π n q.1 (clampT n q) := rfl

/-- The Markov kernel `z ↦ ϕ(· | z, s)`. -/
noncomputable def phiKer {M : Model X A} {phi : X → ℝ → Measure A} (hphi : IsMarkovPolicy M phi)
    {s : ℝ} (hs : 0 < s) : Kernel X A :=
  ⟨fun z => phi z s, Measure.measurable_of_measurable_coe _ fun _ hB => measurable_phi_at hphi hs hB⟩

instance {M : Model X A} {phi : X → ℝ → Measure A} (hphi : IsMarkovPolicy M phi)
    {s : ℝ} (hs : 0 < s) : IsMarkovKernel (phiKer hphi hs) :=
  ⟨fun z => hphi.prob z s hs⟩

end CTJMDPAuxE49

open CTJMDPAuxE49

theorem solution {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (π : Policy X A) (hπ : IsPolicy M π)
    (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (P : Measure (Traj X)) (hP : IsLaw M (Measure.dirac x) π P)
    (h16 : Disintegrates P π phi)
    (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (Z : Set X) (hZ : MeasurableSet Z) :
    (∀ s : ℝ, 0 < s →
      expAt P π s (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, f z a ∂p) =
        ∫⁻ z in Z, (∫⁻ a, f z a ∂(phi z s)) ∂(stateMarg P s)) ∧
    (∀ t : ℝ, 0 < t →
      expPath P π t (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, f z a ∂p) =
        ∫⁻ s in Ioc (0 : ℝ) t,
          expAt P π s (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, f z a ∂p) ∧
      ∫⁻ s in Ioc (0 : ℝ) t,
          expAt P π s (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, f z a ∂p) =
        ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z in Z, (∫⁻ a, f z a ∂(phi z s)) ∂(stateMarg P s)) := by
  have hprob := hP.prob
  -- (49)
  have h49 : ∀ s : ℝ, 0 < s →
      expAt P π s (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, f z a ∂p) =
        ∫⁻ z in Z, (∫⁻ a, f z a ∂(phi z s)) ∂(stateMarg P s) := by
    intro s hs
    let E : ℕ → Set (Traj X) := fun n => {ω | inInt ω n s} ∩ (fun ω => xn ω n) ⁻¹' Z
    have hE : ∀ n, MeasurableSet (E n) := fun n => (measurableSet_inInt n s).inter ((measurable_xn n) hZ)
    let κ : ℕ → Kernel (Traj X) A := fun n => (polKer hπ n).comap (fun ω => (ω, s)) (by fun_prop)
    have hκ : ∀ n, IsMarkovKernel (κ n) := fun n => by infer_instance
    let φ : ℕ → Traj X × A → X × A := fun n q => (xn q.1 n, q.2)
    have hφ : ∀ n, Measurable (φ n) := fun n => ((measurable_xn n).comp measurable_fst).prodMk measurable_snd
    let μL : Measure (X × A) := Measure.sum fun n => ((P.restrict (E n)) ⊗ₘ κ n).map (φ n)
    have hsZ : stateMarg P s Z ≤ 1 :=
      le_trans (measure_mono (subset_univ Z)) (stateMarg_univ_le_one M _ π P hP s)
    have : IsFiniteMeasure (stateMarg P s) :=
      ⟨lt_of_le_of_lt (stateMarg_univ_le_one M _ π P hP s) ENNReal.one_lt_top⟩
    let μR : Measure (X × A) := ((stateMarg P s).restrict Z) ⊗ₘ (phiKer hphi hs)
    have hμRfin : IsFiniteMeasure μR := by
      refine ⟨?_⟩
      simp only [μR]
      rw [Measure.compProd_apply_univ, Measure.restrict_apply_univ]
      exact lt_of_le_of_lt hsZ ENNReal.one_lt_top
    -- the two measures agree on rectangles
    have hrect : ∀ (Z' : Set X) (B : Set A), MeasurableSet Z' → MeasurableSet B →
        μL (Z' ×ˢ B) = μR (Z' ×ˢ B) := by
      intro Z' B hZ' hB
      simp only [μL, μR]
      rw [Measure.sum_apply _ (hZ'.prod hB), Measure.compProd_apply_prod hZ' hB,
        Measure.restrict_restrict hZ']
      show _ = ∫⁻ z in Z' ∩ Z, phi z s B ∂(stateMarg P s)
      rw [← h16 s hs (Z' ∩ Z) B (hZ'.inter hZ) hB]
      unfold saMarg expAt
      congr 1; funext n
      rw [Measure.map_apply (hφ n) (hZ'.prod hB)]
      have hpre : φ n ⁻¹' (Z' ×ˢ B) = ((fun ω => xn ω n) ⁻¹' Z') ×ˢ B := by
        ext q; simp [φ]
      rw [hpre, Measure.compProd_apply_prod ((measurable_xn n) hZ') hB,
        Measure.restrict_restrict ((measurable_xn n) hZ'), ← lintegral_indicator
          (((measurable_xn n) hZ').inter (hE n)), ← lintegral_indicator (measurableSet_inInt n s)]
      congr 1; funext ω
      by_cases hω : inInt ω n s
      · have hκω : κ n ω = π n ω (s - (tn ω n).toReal) := by
          simp only [κ, Kernel.comap_apply, polKer_apply, clampT_eq hω]
        by_cases hz : xn ω n ∈ Z' ∩ Z
        · have : ω ∈ (fun ω => xn ω n) ⁻¹' Z' ∩ E n := ⟨hz.1, hω, hz.2⟩
          simp [indicator_of_mem this, hω, hz, hκω]
        · have : ω ∉ (fun ω => xn ω n) ⁻¹' Z' ∩ E n := fun h => hz ⟨h.1, h.2.2⟩
          simp [indicator_of_notMem this, hω, hz]
      · have : ω ∉ (fun ω => xn ω n) ⁻¹' Z' ∩ E n := fun h => hω h.2.1
        simp [indicator_of_notMem this, hω]
    have hμ : μR = μL := by
      refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
      · rintro _ ⟨Z', hZ', B, hB, rfl⟩
        exact (hrect Z' B hZ' hB).symm
      · rw [← univ_prod_univ]; exact (hrect _ _ MeasurableSet.univ MeasurableSet.univ).symm
    -- integrate `f` against both
    have hR : ∫⁻ q, f q.1 q.2 ∂μR = ∫⁻ z in Z, (∫⁻ a, f z a ∂(phi z s)) ∂(stateMarg P s) := by
      simp only [μR]
      rw [Measure.lintegral_compProd (f := fun q : X × A => f q.1 q.2) hf]
      rfl
    have hL : ∫⁻ q, f q.1 q.2 ∂μL =
        expAt P π s (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, f z a ∂p) := by
      simp only [μL]
      rw [lintegral_sum_measure]
      unfold expAt
      congr 1; funext n
      rw [lintegral_map (f := fun q : X × A => f q.1 q.2) hf (hφ n),
        Measure.lintegral_compProd (f := fun q : Traj X × A => f (φ n q).1 (φ n q).2) (hf.comp (hφ n)),
        ← lintegral_indicator (hE n), ← lintegral_indicator (measurableSet_inInt n s)]
      congr 1; funext ω
      by_cases hω : inInt ω n s
      · have hκω : κ n ω = π n ω (s - (tn ω n).toReal) := by
          simp only [κ, Kernel.comap_apply, polKer_apply, clampT_eq hω]
        by_cases hz : xn ω n ∈ Z
        · have : ω ∈ E n := ⟨hω, hz⟩
          simp [indicator_of_mem this, hω, hz, hκω, φ]
        · have : ω ∉ E n := fun h => hz h.2
          simp [indicator_of_notMem this, hω, hz]
      · have : ω ∉ E n := fun h => hω h.1
        simp [indicator_of_notMem this, hω]
    rw [← hL, ← hR, hμ]
  refine ⟨h49, fun t ht => ⟨?_, ?_⟩⟩
  · -- (50), first equality: Tonelli
    let S : ℕ → Set (Traj X × ℝ) := fun n => {q | 0 < q.2 ∧ q.2 ≤ t ∧ inInt q.1 n q.2}
    have hS : ∀ n, MeasurableSet (S n) := by
      intro n
      show MeasurableSet {q : Traj X × ℝ | 0 < q.2 ∧ q.2 ≤ t ∧
        (tn q.1 n < ENNReal.ofReal q.2 ∧ ENNReal.ofReal q.2 ≤ tn q.1 (n + 1))}
      refine (measurableSet_lt measurable_const measurable_snd).inter
        ((measurableSet_le measurable_snd measurable_const).inter
          ((measurableSet_lt ((measurable_tn n).comp measurable_fst)
            (ENNReal.measurable_ofReal.comp measurable_snd)).inter
          (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd)
            ((measurable_tn (n+1)).comp measurable_fst))))
    let g : ℕ → Traj X × ℝ → ℝ≥0∞ := fun n q =>
      Z.indicator (fun _ => (1 : ℝ≥0∞)) (xn q.1 n) * ∫⁻ a, f (xn q.1 n) a ∂(polKer hπ n q)
    have hg : ∀ n, Measurable (g n) := by
      intro n
      refine Measurable.mul ?_ ?_
      · exact (measurable_const.indicator hZ).comp ((measurable_xn n).comp measurable_fst)
      · refine Measurable.lintegral_kernel_prod_right' (κ := polKer hπ n)
          (f := fun r : (Traj X × ℝ) × A => f (xn r.1.1 n) r.2) ?_
        exact hf.comp (((measurable_xn n).comp (measurable_fst.comp measurable_fst)).prodMk
          measurable_snd)
    let H : ℕ → Traj X × ℝ → ℝ≥0∞ := fun n => (S n).indicator (g n)
    have hH : ∀ n, Measurable (H n) := fun n => (hg n).indicator (hS n)
    have hgq : ∀ n (ω : Traj X) (s : ℝ), inInt ω n s →
        g n (ω, s) = Z.indicator (fun _ => (1 : ℝ≥0∞)) (xn ω n) *
          ∫⁻ a, f (xn ω n) a ∂(π n ω (s - (tn ω n).toReal)) := by
      intro n ω s hω
      simp only [g, polKer_apply, clampT_eq hω]
    unfold expPath expPathAt
    have hL1 : ∀ ω : Traj X, ∀ n, ∫⁻ s in {s : ℝ | 0 < s ∧ s ≤ t ∧ inInt ω n s},
        Z.indicator (fun _ => (1 : ℝ≥0∞)) (xn ω n) *
          ∫⁻ a, f (xn ω n) a ∂(π n ω (s - (tn ω n).toReal)) = ∫⁻ s, H n (ω, s) := by
      intro ω n
      rw [show {s : ℝ | 0 < s ∧ s ≤ t ∧ inInt ω n s} = Prod.mk ω ⁻¹' S n from rfl,
        ← lintegral_indicator (measurable_prodMk_left (hS n))]
      congr 1; funext s
      by_cases hs : 0 < s ∧ s ≤ t ∧ inInt ω n s
      · have h1 : s ∈ Prod.mk ω ⁻¹' S n := hs
        have h2 : (ω, s) ∈ S n := hs
        rw [indicator_of_mem h1, show H n (ω, s) = g n (ω, s) from indicator_of_mem h2 _,
          hgq n ω s hs.2.2]
      · have h1 : s ∉ Prod.mk ω ⁻¹' S n := hs
        have h2 : (ω, s) ∉ S n := hs
        rw [indicator_of_notMem h1, show H n (ω, s) = 0 from indicator_of_notMem h2 _]
    simp_rw [hL1]
    rw [lintegral_tsum (fun n => (hH n).lintegral_prod_right'.aemeasurable)]
    have hswap : ∀ n, ∫⁻ ω, ∫⁻ s, H n (ω, s) ∂volume ∂P = ∫⁻ s, ∫⁻ ω, H n (ω, s) ∂P ∂volume :=
      fun n => lintegral_lintegral_swap (f := fun ω s => H n (ω, s)) (hH n).aemeasurable
    simp_rw [hswap]
    rw [← lintegral_tsum (fun n => (hH n).lintegral_prod_left'.aemeasurable)]
    rw [← lintegral_indicator measurableSet_Ioc]
    congr 1; funext s
    unfold expAt
    by_cases hs : s ∈ Ioc (0 : ℝ) t
    · rw [indicator_of_mem hs]
      congr 1; funext n
      rw [← lintegral_indicator (measurableSet_inInt n s)]
      congr 1; funext ω
      by_cases hω : inInt ω n s
      · have h2 : (ω, s) ∈ S n := ⟨hs.1, hs.2, hω⟩
        rw [show H n (ω, s) = g n (ω, s) from indicator_of_mem h2 _,
          indicator_of_mem (show ω ∈ {ω | inInt ω n s} from hω), hgq n ω s hω]
      · have h2 : (ω, s) ∉ S n := fun h => hω h.2.2
        rw [show H n (ω, s) = 0 from indicator_of_notMem h2 _,
          indicator_of_notMem (show ω ∉ {ω | inInt ω n s} from hω)]
    · rw [indicator_of_notMem hs]
      refine ENNReal.tsum_eq_zero.2 fun n => ?_
      have h0 : ∀ ω, H n (ω, s) = 0 := fun ω => indicator_of_notMem (fun h => hs ⟨h.1, h.2.1⟩) _
      simp [h0]
  · exact setLIntegral_congr_fun measurableSet_Ioc (fun s hs => h49 s hs.1)
