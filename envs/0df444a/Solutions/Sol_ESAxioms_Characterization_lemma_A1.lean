-- Prove2me | solution 1 for ESAxioms.Characterization.lemma_A1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:36:45.592412+00:00
-- url     : https://prove2.me/submissions/e7fde508-9808-4124-bd2c-6c28e80cd474

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Halving inside a set: subsets of arbitrarily small positive probability. -/
lemma exists_small_sub (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (S : Set Ω) (hS : MeasurableSet S)
    (hSpos : 0 < P.real S) (n : ℕ) :
    ∃ B ⊆ S, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ (1/2 : ℝ) ^ n * P.real S := by
  induction n with
  | zero => exact ⟨S, le_rfl, hS, hSpos, by simp⟩
  | succ n ih =>
    obtain ⟨B, hBS, hB, hpos, hle⟩ := ih
    have hB' : 0 < P B := by
      rw [measureReal_def] at hpos
      exact ENNReal.toReal_pos_iff.mp hpos |>.1
    obtain ⟨t, htB, ht, ht0, htlt⟩ := hP B hB hB'
    have ht0' : 0 < P.real t := by
      rw [measureReal_def]; exact ENNReal.toReal_pos ht0.ne' (measure_ne_top _ _)
    have htlt' : P.real t < P.real B := by
      rw [measureReal_def, measureReal_def]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr htlt
    have hd : P.real (B \ t) = P.real B - P.real t := measureReal_sdiff htB ht
    by_cases h : P.real t ≤ P.real B / 2
    · refine ⟨t, htB.trans hBS, ht, ht0', ?_⟩
      rw [pow_succ]; nlinarith
    · refine ⟨B \ t, Set.diff_subset.trans hBS, hB.diff ht, by rw [hd]; linarith, ?_⟩
      rw [hd, pow_succ]; push Not at h; nlinarith

lemma exists_small_sub' (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (S : Set Ω) (hS : MeasurableSet S)
    (hSpos : 0 < P.real S) (ε : ℝ) (hε : 0 < ε) :
    ∃ B ⊆ S, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ ε := by
  have hS1 : P.real S ≤ 1 := by
    have := measureReal_mono (μ := P) (Set.subset_univ S) (measure_ne_top _ _)
    rwa [probReal_univ] at this
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ) < 1)
  obtain ⟨B, hBS, hB, hpos, hle⟩ := exists_small_sub P hP S hS hSpos n
  refine ⟨B, hBS, hB, hpos, ?_⟩
  have : (1/2:ℝ) ^ n * P.real S ≤ (1/2) ^ n := by
    have : 0 ≤ (1/2:ℝ) ^ n := by positivity
    nlinarith
  linarith

lemma step_exists (P : Measure Ω) [IsProbabilityMeasure P] (S : Set Ω) (t : ℝ) (T : Set Ω) :
    ∃ U : Set Ω, (MeasurableSet T → T ⊆ S → P.real T ≤ t →
      (MeasurableSet U ∧ U ⊆ S \ T ∧ P.real T + P.real U ≤ t ∧
        ∀ V, MeasurableSet V → V ⊆ S \ T → P.real T + P.real V ≤ t → P.real V ≤ 2 * P.real U)) := by
  by_cases hT : MeasurableSet T ∧ T ⊆ S ∧ P.real T ≤ t
  · obtain ⟨hTm, hTS, hTt⟩ := hT
    set adm : Set ℝ := {r | ∃ U, MeasurableSet U ∧ U ⊆ S \ T ∧ P.real T + P.real U ≤ t ∧
      r = P.real U} with hadm
    have hne : adm.Nonempty := ⟨0, ∅, MeasurableSet.empty, Set.empty_subset _, by simpa using hTt,
      by simp⟩
    have hbdd : BddAbove adm := ⟨1, fun r ⟨U, _, _, _, hr⟩ => by
      rw [hr]
      have := measureReal_mono (μ := P) (Set.subset_univ U) (measure_ne_top _ _)
      rwa [probReal_univ] at this⟩
    set s := sSup adm with hs
    have hle : ∀ V, MeasurableSet V → V ⊆ S \ T → P.real T + P.real V ≤ t → P.real V ≤ s :=
      fun V hV hVS hVt => le_csSup hbdd ⟨V, hV, hVS, hVt, rfl⟩
    have hs0 : 0 ≤ s := le_csSup_of_le hbdd ⟨∅, MeasurableSet.empty, Set.empty_subset _,
      by simpa using hTt, by simp⟩ le_rfl
    rcases eq_or_lt_of_le hs0 with h0 | hpos
    · refine ⟨∅, fun _ _ _ => ⟨MeasurableSet.empty, Set.empty_subset _, by simpa using hTt, ?_⟩⟩
      intro V hV hVS hVt
      have := hle V hV hVS hVt
      simp; linarith
    · obtain ⟨r, ⟨U, hU, hUS, hUt, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hne (half_lt_self hpos)
      refine ⟨U, fun _ _ _ => ⟨hU, hUS, hUt, ?_⟩⟩
      intro V hV hVS hVt
      have := hle V hV hVS hVt
      linarith
  · exact ⟨∅, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hT⟩

/-- Sierpiński's theorem: in an atomless probability space every value in `[0, ℙ(S)]` is the
probability of a measurable subset of `S`. -/
theorem sierpinski (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (S : Set Ω) (hS : MeasurableSet S)
    (t : ℝ) (ht0 : 0 ≤ t) (htS : t ≤ P.real S) :
    ∃ T ⊆ S, MeasurableSet T ∧ P.real T = t := by
  choose g hg using step_exists P S t
  let T : ℕ → Set Ω := fun n => Nat.rec ∅ (fun _ Tn => Tn ∪ g Tn) n
  have hT0 : T 0 = ∅ := rfl
  have hTs : ∀ n, T (n + 1) = T n ∪ g (T n) := fun n => rfl
  have inv : ∀ n, MeasurableSet (T n) ∧ T n ⊆ S ∧ P.real (T n) ≤ t := by
    intro n
    induction n with
    | zero => rw [hT0]; exact ⟨MeasurableSet.empty, Set.empty_subset _, by simpa using ht0⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨hU, hUS, hUt, -⟩ := hg (T n) h1 h2 h3
      have hdisj : Disjoint (T n) (g (T n)) :=
        Set.disjoint_left.mpr fun ω h1 h2 => (hUS h2).2 h1
      rw [hTs]
      refine ⟨h1.union hU, Set.union_subset h2 (hUS.trans Set.diff_subset), ?_⟩
      rw [measureReal_union hdisj hU]; exact hUt
  have hadd : ∀ n, P.real (T (n+1)) = P.real (T n) + P.real (g (T n)) := by
    intro n
    obtain ⟨h1, h2, h3⟩ := inv n
    obtain ⟨hU, hUS, -, -⟩ := hg (T n) h1 h2 h3
    have hdisj : Disjoint (T n) (g (T n)) :=
      Set.disjoint_left.mpr fun ω h1 h2 => (hUS h2).2 h1
    rw [hTs, measureReal_union hdisj hU]
  have hmono : Monotone T := monotone_nat_of_le_succ fun n => by
    rw [hTs]; exact Set.subset_union_left
  set Tinf := ⋃ n, T n with hTinf
  have hTinfm : MeasurableSet Tinf := MeasurableSet.iUnion fun n => (inv n).1
  have hTinfS : Tinf ⊆ S := Set.iUnion_subset fun n => (inv n).2.1
  have hlim : Tendsto (fun n => P.real (T n)) atTop (𝓝 (P.real Tinf)) := by
    have := tendsto_measure_iUnion_atTop (μ := P) hmono
    have := (ENNReal.tendsto_toReal (measure_ne_top P Tinf)).comp this
    simpa [Function.comp_def, measureReal_def] using this
  have hTinft : P.real Tinf ≤ t := le_of_tendsto' hlim fun n => (inv n).2.2
  refine ⟨Tinf, hTinfS, hTinfm, ?_⟩
  by_contra hne
  have hlt : P.real Tinf < t := lt_of_le_of_ne hTinft hne
  -- increments tend to zero
  have hinc : Tendsto (fun n => P.real (g (T n))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => P.real (T (n+1)) - P.real (T n)) atTop
        (𝓝 (P.real Tinf - P.real Tinf)) :=
      (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    rw [sub_self] at h1
    refine h1.congr fun n => ?_
    show P.real (T (n+1)) - P.real (T n) = P.real (g (T n))
    rw [hadd n]; ring
  have hrest : 0 < P.real (S \ Tinf) := by
    rw [measureReal_sdiff hTinfS hTinfm]; linarith
  obtain ⟨V, hVS, hV, hVpos, hVle⟩ :=
    exists_small_sub' P hP (S \ Tinf) (hS.diff hTinfm) hrest (t - P.real Tinf) (by linarith)
  have hbound : ∀ n, P.real V ≤ 2 * P.real (g (T n)) := by
    intro n
    obtain ⟨h1, h2, h3⟩ := inv n
    obtain ⟨-, -, -, hmax⟩ := hg (T n) h1 h2 h3
    apply hmax V hV
    · intro ω hω
      exact ⟨(hVS hω).1, fun h => (hVS hω).2 (Set.mem_iUnion.mpr ⟨n, h⟩)⟩
    · have : P.real (T n) ≤ P.real Tinf :=
        measureReal_mono (Set.subset_iUnion T n) (measure_ne_top _ _)
      linarith
  have h2 : Tendsto (fun n => 2 * P.real (g (T n))) atTop (𝓝 0) := by
    simpa using hinc.const_mul 2
  have := ge_of_tendsto h2 (Eventually.of_forall hbound)
  linarith

end ESAxAtomless

namespace ESAxA1Aux

open ESAxioms.Characterization ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

lemma sameLaw_of_ae (P : Measure Ω) {X Y : Ω → ℝ} (h : X =ᵐ[P] Y) : SameLaw P X Y := by
  intro x
  apply measureReal_congr
  filter_upwards [h] with ω hω
  show (X ω ≤ x) = (Y ω ≤ x)
  rw [hω]

/-- `𝟙_B`. -/
noncomputable def I (B : Set Ω) : Ω → ℝ := B.indicator (fun _ => (1:ℝ))

lemma I_nonneg (B : Set Ω) (ω : Ω) : 0 ≤ I B ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω

lemma I_le_one (B : Set Ω) (ω : Ω) : I B ω ≤ 1 := by
  unfold I; by_cases h : ω ∈ B <;> simp [h]

lemma I_mem (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) (hB : MeasurableSet B) :
    I B ∈ L1Plus P :=
  ⟨⟨measurable_const.indicator hB, (integrable_const (1:ℝ)).indicator hB⟩, I_nonneg B⟩

lemma distFn_I (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) (hB : MeasurableSet B)
    (x : ℝ) : TailRiskSharing.VaRConv.distFn P (I B) x =
      if x < 0 then 0 else if x < 1 then 1 - P.real B else 1 := by
  unfold TailRiskSharing.VaRConv.distFn
  split_ifs with h1 h2
  · have : {ω | I B ω ≤ x} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le h1 (I_nonneg B ω)
    rw [this]; simp
  · have : {ω | I B ω ≤ x} = Bᶜ := by
      ext ω; unfold I; by_cases h : ω ∈ B <;> simp [h] <;> push Not at h1 <;> linarith
    rw [this, probReal_compl_eq_one_sub hB]
  · have : {ω | I B ω ≤ x} = Set.univ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      push Not at h2; exact le_trans (I_le_one B ω) h2
    rw [this, probReal_univ]

lemma sameLaw_I (P : Measure Ω) [IsProbabilityMeasure P] (B C : Set Ω) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (h : P.real B = P.real C) : SameLaw P (I B) (I C) := by
  intro x; rw [distFn_I P B hB, distFn_I P C hC, h]

lemma smul_mem (P : Measure Ω) {X : Ω → ℝ} (hX : X ∈ L1Plus P) (c : ℝ) (hc : 0 ≤ c) :
    c • X ∈ L1Plus P :=
  ⟨⟨hX.1.1.const_smul c, hX.1.2.smul c⟩, fun ω => mul_nonneg hc (hX.2 ω)⟩

lemma add_mem (P : Measure Ω) {X Y : Ω → ℝ} (hX : X ∈ L1Plus P) (hY : Y ∈ L1Plus P) :
    X + Y ∈ L1Plus P :=
  ⟨⟨hX.1.1.add hY.1.1, hX.1.2.add hY.1.2⟩, fun ω => add_nonneg (hX.2 ω) (hY.2 ω)⟩

lemma zero_mem (P : Measure Ω) : (0 : Ω → ℝ) ∈ L1Plus P :=
  ⟨⟨measurable_const, integrable_zero _ _ _⟩, fun _ => le_rfl⟩

section
variable (P : Measure Ω) [IsProbabilityMeasure P] (ρ : (Ω → ℝ) → ℝ)
  (hM : AxiomM (L1Plus P) ρ) (hA : IsAdditiveOn (L1Plus P) ρ)

include hA in
lemma rho_zero : ρ 0 = 0 := by
  have := hA 0 (zero_mem P) 0 (zero_mem P)
  rw [add_zero] at this; linarith

include hM hA in
lemma rho_nonneg {X : Ω → ℝ} (hX : X ∈ L1Plus P) : 0 ≤ ρ X := by
  have := hM 0 (zero_mem P) X hX hX.2
  rwa [rho_zero P ρ hA] at this

include hA in
lemma rho_nat {X : Ω → ℝ} (hX : X ∈ L1Plus P) (n : ℕ) : ρ ((n:ℝ) • X) = n * ρ X := by
  induction n with
  | zero => simp [rho_zero P ρ hA]
  | succ n ih =>
    have e : ((n + 1 : ℕ) : ℝ) • X = (n:ℝ) • X + X := by
      push_cast; rw [add_smul, one_smul]
    rw [e, hA _ (smul_mem P hX _ (Nat.cast_nonneg n)) _ hX, ih]; push_cast; ring

include hA in
lemma rho_natdiv {X : Ω → ℝ} (hX : X ∈ L1Plus P) (k n : ℕ) (hn : 0 < n) :
    ρ (((k:ℝ) / n) • X) = (k / n) * ρ X := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : ρ X = n * ρ ((1 / (n:ℝ)) • X) := by
    rw [← rho_nat P ρ hA (smul_mem P hX _ (by positivity)) n, smul_smul, mul_one_div_cancel hn',
      one_smul]
  have h2 : ((k:ℝ) / n) • X = (k:ℝ) • ((1 / (n:ℝ)) • X) := by
    rw [smul_smul]; congr 1; ring
  rw [h2, rho_nat P ρ hA (smul_mem P hX _ (by positivity)) k, h1]
  field_simp

include hM hA in
lemma rho_smul {X : Ω → ℝ} (hX : X ∈ L1Plus P) (c : ℝ) (hc : 0 ≤ c) :
    ρ (c • X) = c * ρ X := by
  have hρX := rho_nonneg P ρ hM hA hX
  have mono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ρ (a • X) ≤ ρ (b • X) := by
    intro a b ha hab
    apply hM _ (smul_mem P hX a ha) _ (smul_mem P hX b (le_trans ha hab))
    intro ω; simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right hab (hX.2 ω)
  have key : ∀ n : ℕ, 0 < n → |ρ (c • X) - c * ρ X| ≤ ρ X / n := by
    intro n hn
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    set k := ⌊c * n⌋₊ with hk
    have hk1 : (k:ℝ) ≤ c * n := Nat.floor_le (by positivity)
    have hk2 : c * n < k + 1 := Nat.lt_floor_add_one _
    have lo : ρ (((k:ℝ) / n) • X) ≤ ρ (c • X) :=
      mono _ _ (by positivity) (by rw [div_le_iff₀ hn']; linarith)
    have hi : ρ (c • X) ≤ ρ ((((k + 1 : ℕ) : ℝ) / n) • X) :=
      mono _ _ hc (by rw [le_div_iff₀ hn']; push_cast; linarith)
    rw [rho_natdiv P ρ hA hX k n hn] at lo
    rw [rho_natdiv P ρ hA hX (k + 1) n hn] at hi
    push_cast at hi
    rw [abs_le]
    have e1 : (k:ℝ) / n ≥ c - 1 / n := by
      rw [ge_iff_le, show c - 1 / (n:ℝ) = (c * n - 1) / n by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hn'.le
    have e2 : ((k:ℝ) + 1) / n ≤ c + 1 / n := by
      rw [show c + 1 / (n:ℝ) = (c * n + 1) / n by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hn'.le
    constructor
    · have : (c - 1 / n) * ρ X ≤ (k / n) * ρ X := mul_le_mul_of_nonneg_right e1 hρX
      have : ρ X / n = 1 / n * ρ X := by ring
      nlinarith
    · have : ((k + 1) / n) * ρ X ≤ (c + 1 / n) * ρ X := mul_le_mul_of_nonneg_right e2 hρX
      have : ρ X / n = 1 / n * ρ X := by ring
      nlinarith
  apply eq_of_abs_sub_nonpos
  by_contra hpos
  push Not at hpos
  obtain ⟨n, hn⟩ := exists_nat_gt (ρ X / |ρ (c • X) - c * ρ X|)
  have hn0 : 0 < n := by
    have : 0 ≤ ρ X / |ρ (c • X) - c * ρ X| := div_nonneg hρX (abs_nonneg _)
    exact_mod_cast lt_of_le_of_lt this hn
  have := key n hn0
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  rw [div_lt_iff₀ hpos] at hn
  rw [le_div_iff₀ hn'] at this
  linarith

end

end ESAxA1Aux

namespace ESAxA1Aux

open ESAxioms.Characterization ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

lemma I_union (B C : Set Ω) (h : Disjoint B C) : I (B ∪ C) = I B + I C := by
  unfold I; ext ω; simp [Set.indicator_union_of_disjoint h]

lemma I_mono {B C : Set Ω} (h : B ⊆ C) (ω : Ω) : I B ω ≤ I C ω := by
  unfold I
  exact Set.indicator_le_indicator_of_subset h (fun _ => zero_le_one) ω

lemma real_le_one (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) : P.real B ≤ 1 := by
  have := measureReal_mono (μ := P) (Set.subset_univ B) (measure_ne_top _ _)
  rwa [probReal_univ] at this

section
variable (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
  (ρ : (Ω → ℝ) → ℝ)
  (hM : AxiomM (L1Plus P) ρ) (hA : IsAdditiveOn (L1Plus P) ρ) (hLI : AxiomLI P (L1Plus P) ρ)

include hLI in
lemma rho_I_eq (B C : Set Ω) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (h : P.real B = P.real C) : ρ (I B) = ρ (I C) :=
  hLI _ (I_mem P B hB) _ (I_mem P C hC) (sameLaw_I P B C hB hC h)

include hP hM hA hLI in
lemma rho_I (B : Set Ω) (hB : MeasurableSet B) : ρ (I B) = ρ (I Set.univ) * P.real B := by
  set lam := ρ (I Set.univ) with hlam
  have hex : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 → ∃ B : Set Ω, MeasurableSet B ∧ P.real B = t := by
    intro t ht
    obtain ⟨T, -, hT, hPT⟩ := sierpinski P hP Set.univ MeasurableSet.univ t ht.1
      (by rw [probReal_univ]; exact ht.2)
    exact ⟨T, hT, hPT⟩
  classical
  let T : ℝ → Set Ω := fun t => if h : 0 ≤ t ∧ t ≤ 1 then Classical.choose (hex t h) else ∅
  have hT : ∀ t, 0 ≤ t → t ≤ 1 → MeasurableSet (T t) ∧ P.real (T t) = t := by
    intro t h0 h1
    have h : 0 ≤ t ∧ t ≤ 1 := ⟨h0, h1⟩
    simp only [T, dif_pos h]
    exact Classical.choose_spec (hex t h)
  let g : ℝ → ℝ := fun t => ρ (I (T t))
  have g_spec : ∀ B, MeasurableSet B → ρ (I B) = g (P.real B) := by
    intro B hB
    have h := hT (P.real B) measureReal_nonneg (real_le_one P B)
    exact rho_I_eq P ρ hLI B _ hB h.1 h.2.symm
  have g_add : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ 1 → g (s + t) = g s + g t := by
    intro s t hs ht hst
    obtain ⟨hBm, hPB⟩ := hT s hs (by linarith)
    obtain ⟨C, hCB, hCm, hPC⟩ := sierpinski P hP (T s)ᶜ hBm.compl t ht
      (by rw [probReal_compl_eq_one_sub hBm, hPB]; linarith)
    have hdisj : Disjoint (T s) C := Set.disjoint_left.mpr fun ω h1 h2 => hCB h2 h1
    have hU : P.real (T s ∪ C) = s + t := by rw [measureReal_union hdisj hCm, hPB, hPC]
    rw [← hU, ← g_spec _ (hBm.union hCm), I_union _ _ hdisj,
      hA _ (I_mem P _ hBm) _ (I_mem P _ hCm), g_spec _ hBm, g_spec _ hCm, hPB, hPC]
  have g_mono : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → g s ≤ g t := by
    intro s t hs hst ht
    obtain ⟨hCm, hPC⟩ := hT t (le_trans hs hst) ht
    obtain ⟨B, hBC, hBm, hPB⟩ := sierpinski P hP (T t) hCm s hs (by rw [hPC]; exact hst)
    rw [← hPB, ← g_spec _ hBm]
    exact hM _ (I_mem P _ hBm) _ (I_mem P _ hCm) (I_mono hBC)
  have g_one : g 1 = lam := by
    rw [hlam, g_spec _ MeasurableSet.univ, probReal_univ]
  have g_zero : g 0 = 0 := by
    have := g_add 0 0 le_rfl le_rfl (by norm_num)
    simp only [add_zero] at this; linarith
  have g_nat : ∀ k : ℕ, ∀ s, 0 ≤ s → (k:ℝ) * s ≤ 1 → g (k * s) = k * g s := by
    intro k
    induction k with
    | zero => intro s _ _; simp [g_zero]
    | succ k ih =>
      intro s hs hks
      push_cast at hks ⊢
      have h1 : (k:ℝ) * s ≤ 1 := by nlinarith
      rw [add_mul, one_mul, g_add _ _ (by positivity) hs (by linarith), ih s hs h1]; ring
  have lam_nonneg : 0 ≤ lam := rho_nonneg P ρ hM hA (I_mem P _ MeasurableSet.univ)
  have g_frac : ∀ n k : ℕ, 0 < n → k ≤ n → g ((k:ℝ) / n) = k / n * lam := by
    intro n k hn hkn
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have h1 : g 1 = n * g (1 / n) := by
      rw [← g_nat n (1 / n) (by positivity) (by rw [mul_one_div_cancel hn'.ne'])]
      rw [mul_one_div_cancel hn'.ne']
    have hk : (k:ℝ) ≤ n := by exact_mod_cast hkn
    have h2 : g ((k:ℝ) / n) = k * g (1 / n) := by
      rw [← g_nat k (1 / n) (by positivity) (by rw [mul_one_div, div_le_one hn']; exact hk)]
      rw [mul_one_div]
    rw [h2, g_one] at *
    rw [h1]; field_simp
  have g_lin : ∀ t, 0 ≤ t → t ≤ 1 → g t = lam * t := by
    intro t h0 h1
    rcases eq_or_lt_of_le h1 with heq | hlt
    · rw [heq, g_one, mul_one]
    have key : ∀ n : ℕ, 0 < n → |g t - lam * t| ≤ lam / n := by
      intro n hn
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      set k := ⌊t * n⌋₊ with hk
      have hk1 : (k:ℝ) ≤ t * n := Nat.floor_le (by positivity)
      have hk2 : t * n < k + 1 := Nat.lt_floor_add_one _
      have hkn : k + 1 ≤ n := by
        have : (k:ℝ) < n := by nlinarith
        exact_mod_cast this
      have lo := g_mono ((k:ℝ) / n) t (by positivity) (by rw [div_le_iff₀ hn']; linarith) h1
      have hi := g_mono t (((k + 1 : ℕ):ℝ) / n) h0
        (by rw [le_div_iff₀ hn']; push_cast; linarith)
        (by rw [div_le_one hn']; exact_mod_cast hkn)
      rw [g_frac n k hn (by omega)] at lo
      rw [g_frac n (k + 1) hn hkn] at hi
      push_cast at hi
      have e1 : (k:ℝ) / n ≥ t - 1 / n := by
        rw [ge_iff_le, show t - 1 / (n:ℝ) = (t * n - 1) / n by field_simp]
        exact div_le_div_of_nonneg_right (by linarith) hn'.le
      have e2 : ((k:ℝ) + 1) / n ≤ t + 1 / n := by
        rw [show t + 1 / (n:ℝ) = (t * n + 1) / n by field_simp]
        exact div_le_div_of_nonneg_right (by linarith) hn'.le
      rw [abs_le]
      have hl : lam / n = 1 / n * lam := by ring
      constructor
      · have := mul_le_mul_of_nonneg_right e1 lam_nonneg
        nlinarith
      · have := mul_le_mul_of_nonneg_right e2 lam_nonneg
        nlinarith
    apply eq_of_abs_sub_nonpos
    by_contra hpos
    push Not at hpos
    obtain ⟨n, hn⟩ := exists_nat_gt (lam / |g t - lam * t|)
    have hn0 : 0 < n := by
      have : 0 ≤ lam / |g t - lam * t| := div_nonneg lam_nonneg (abs_nonneg _)
      exact_mod_cast lt_of_le_of_lt this hn
    have := key n hn0
    have hn' : (0:ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hpos] at hn
    rw [le_div_iff₀ hn'] at this
    linarith
  rw [g_spec B hB, g_lin _ measureReal_nonneg (real_le_one P B)]

end

end ESAxA1Aux

namespace ESAxA1Aux

open ESAxioms.Characterization ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_I (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) (hB : MeasurableSet B) :
    ∫ ω, I B ω ∂P = P.real B := by
  unfold I; rw [integral_indicator_const _ hB]; simp

lemma sum_mem (P : Measure Ω) {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, f i ∈ L1Plus P) : (∑ i ∈ s, f i) ∈ L1Plus P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem P
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact add_mem P (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma rho_sum (P : Measure Ω) [IsProbabilityMeasure P] (ρ : (Ω → ℝ) → ℝ) (hA : IsAdditiveOn (L1Plus P) ρ)
    {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, f i ∈ L1Plus P) : ρ (∑ i ∈ s, f i) = ∑ i ∈ s, ρ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rho_zero P ρ hA
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [hA _ (hf a (Finset.mem_insert_self a s)) _
      (sum_mem P s f fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Counting lemma for the layer sums. -/
lemma card_filter_le (N : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hyN : y ≤ N) :
    ((Finset.range N).filter (fun k : ℕ => ((k:ℝ) + 1) ≤ y)).card = ⌊y⌋₊ := by
  have : (Finset.range N).filter (fun k : ℕ => ((k:ℝ) + 1) ≤ y) = Finset.range ⌊y⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    have hfl : ⌊y⌋₊ ≤ N := Nat.floor_le_of_le hyN
    constructor
    · rintro ⟨_, hk⟩
      have : k + 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hk)
      omega
    · intro hk
      refine ⟨by omega, ?_⟩
      have : k + 1 ≤ ⌊y⌋₊ := hk
      have h2 : ((k + 1 : ℕ) : ℝ) ≤ y := (Nat.le_floor_iff hy0).mp this
      exact_mod_cast h2
  rw [this, Finset.card_range]

section
variable (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
  (ρ : (Ω → ℝ) → ℝ)
  (hM : AxiomM (L1Plus P) ρ) (hA : IsAdditiveOn (L1Plus P) ρ) (hLI : AxiomLI P (L1Plus P) ρ)

include hP hM hA hLI in
lemma rho_bounded (X : Ω → ℝ) (hX : X ∈ L1Plus P) (M : ℕ) (hXM : ∀ ω, X ω ≤ M) :
    ρ X = ρ (I Set.univ) * ∫ ω, X ω ∂P := by
  set lam := ρ (I Set.univ) with hlam
  have lam_nonneg : 0 ≤ lam := rho_nonneg P ρ hM hA (I_mem P _ MeasurableSet.univ)
  have hB : ∀ n k : ℕ, MeasurableSet {ω | ((k:ℝ) + 1) / 2 ^ n ≤ X ω} :=
    fun n k => measurableSet_le measurable_const hX.1.1
  set S : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range (M * 2 ^ n),
    (1 / (2:ℝ) ^ n) • I {ω | ((k:ℝ) + 1) / 2 ^ n ≤ X ω} with hS
  have hSmem : ∀ n, S n ∈ L1Plus P := fun n =>
    sum_mem P _ _ fun k _ => smul_mem P (I_mem P _ (hB n k)) _ (by positivity)
  have hSρ : ∀ n, ρ (S n) = lam * ∫ ω, S n ω ∂P := by
    intro n
    simp only [hS]
    rw [rho_sum P ρ hA _ _ fun k _ => smul_mem P (I_mem P _ (hB n k)) _ (by positivity)]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun k _ => (I_mem P _ (hB n k)).1.2.smul (1 / (2:ℝ) ^ n)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [rho_smul P ρ hM hA (I_mem P _ (hB n k)) _ (by positivity),
      rho_I P hP ρ hM hA hLI _ (hB n k)]
    simp only [Pi.smul_apply]
    rw [integral_smul, integral_I P _ (hB n k), smul_eq_mul]
    ring
  have hSval : ∀ n ω, S n ω = (⌊(2:ℝ) ^ n * X ω⌋₊ : ℝ) / 2 ^ n := by
    intro n ω
    simp only [hS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    have h2n : (0:ℝ) < 2 ^ n := by positivity
    have : ∀ k ∈ Finset.range (M * 2 ^ n), I {ω | ((k:ℝ) + 1) / 2 ^ n ≤ X ω} ω =
        if ((k:ℝ) + 1) ≤ 2 ^ n * X ω then 1 else 0 := by
      intro k _
      unfold I
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      congr 1
      apply propext
      rw [div_le_iff₀ h2n, mul_comm]
    rw [Finset.sum_congr rfl this, Finset.sum_boole]
    rw [card_filter_le (M * 2 ^ n) _ (by have := hX.2 ω; positivity)
      (by push_cast; have := hXM ω; nlinarith)]
    ring
  have hSle : ∀ n ω, S n ω ≤ X ω := by
    intro n ω
    rw [hSval, div_le_iff₀ (by positivity), mul_comm]
    exact Nat.floor_le (by have := hX.2 ω; positivity)
  have hSge : ∀ n ω, X ω - 1 / 2 ^ n ≤ S n ω := by
    intro n ω
    rw [hSval]
    have h2n : (0:ℝ) < 2 ^ n := by positivity
    have := Nat.lt_floor_add_one ((2:ℝ) ^ n * X ω)
    rw [show X ω - 1 / 2 ^ n = (2 ^ n * X ω - 1) / 2 ^ n by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) h2n.le
  have hconst : ∀ c : ℝ, 0 ≤ c → ρ (c • I Set.univ) = c * lam := fun c hc =>
    rho_smul P ρ hM hA (I_mem P _ MeasurableSet.univ) c hc
  have key : ∀ n : ℕ, |ρ X - lam * ∫ ω, X ω ∂P| ≤ lam * (1 / 2 ^ n) := by
    intro n
    have hint1 : ∫ ω, S n ω ∂P ≤ ∫ ω, X ω ∂P :=
      integral_mono (hSmem n).1.2 hX.1.2 (hSle n)
    have hint2 : ∫ ω, X ω ∂P - 1 / 2 ^ n ≤ ∫ ω, S n ω ∂P := by
      have := integral_mono (hX.1.2.sub (integrable_const (1 / (2:ℝ) ^ n))) (hSmem n).1.2
        (fun ω => hSge n ω)
      rw [show (X - fun _ => 1 / (2:ℝ) ^ n) = fun ω => X ω - 1 / (2:ℝ) ^ n from rfl,
        integral_sub hX.1.2 (integrable_const _), integral_const] at this
      simpa using this
    have lo : ρ (S n) ≤ ρ X := hM _ (hSmem n) _ hX (hSle n)
    have hmem2 : S n + (1 / (2:ℝ) ^ n) • I Set.univ ∈ L1Plus P :=
      add_mem P (hSmem n) (smul_mem P (I_mem P _ MeasurableSet.univ) _ (by positivity))
    have hi : ρ X ≤ ρ (S n + (1 / (2:ℝ) ^ n) • I Set.univ) := by
      apply hM _ hX _ hmem2
      intro ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, I, Set.indicator_univ, mul_one]
      linarith [hSge n ω]
    rw [hA _ (hSmem n) _ (smul_mem P (I_mem P _ MeasurableSet.univ) _ (by positivity)),
      hconst _ (by positivity), hSρ] at hi
    rw [hSρ] at lo
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hint2 lam_nonneg]
    · nlinarith [mul_le_mul_of_nonneg_left hint1 lam_nonneg]
  have hlim : Tendsto (fun n : ℕ => lam * (1 / (2:ℝ) ^ n)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (1 / (2:ℝ)) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [one_div_pow] using this.const_mul lam
  have := ge_of_tendsto' hlim key
  have h0 := abs_nonneg (ρ X - lam * ∫ ω, X ω ∂P)
  have : |ρ X - lam * ∫ ω, X ω ∂P| = 0 := le_antisymm (by linarith) h0
  rw [abs_eq_zero, sub_eq_zero] at this
  exact this

end

end ESAxA1Aux

namespace ESAxA1Aux

open ESAxioms.Characterization ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

lemma map_eq_of_sameLaw (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (h : SameLaw P X Y) : P.map X = P.map Y := by
  have _h1 : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hX measurableSet_Iic, Measure.map_apply hY measurableSet_Iic,
    ← ofReal_measureReal (μ := P) (s := X ⁻¹' Set.Iic x),
    ← ofReal_measureReal (μ := P) (s := Y ⁻¹' Set.Iic x)]
  have := h x
  simp only [TailRiskSharing.VaRConv.distFn] at this
  exact congrArg ENNReal.ofReal this

lemma integral_eq_of_sameLaw (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (h : SameLaw P X Y) :
    ∫ ω, X ω ∂P = ∫ ω, Y ω ∂P := by
  have e := map_eq_of_sameLaw P X Y hX hY h
  have h1 : ∫ x, x ∂(P.map X) = ∫ ω, X ω ∂P := integral_map hX.aemeasurable aestronglyMeasurable_id
  have h2 : ∫ x, x ∂(P.map Y) = ∫ ω, Y ω ∂P := integral_map hY.aemeasurable aestronglyMeasurable_id
  rw [← h1, ← h2, e]

section
variable (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
  (ρ : (Ω → ℝ) → ℝ)
  (hM : AxiomM (L1Plus P) ρ) (hA : IsAdditiveOn (L1Plus P) ρ) (hLI : AxiomLI P (L1Plus P) ρ)

include hM hA hLI in
/-- Automatic boundedness of a positive additive law-invariant functional. -/
lemma rho_bound : ∃ C : ℝ, ∀ Y ∈ L1Plus P, ρ Y ≤ C * ∫ ω, Y ω ∂P := by
  by_contra h
  push Not at h
  choose Y hY hYρ using fun n : ℕ => h ((4:ℝ) ^ n)
  have hEpos : ∀ n, 0 < ∫ ω, Y n ω ∂P := by
    intro n
    by_contra hle
    push Not at hle
    have h0 : ∫ ω, Y n ω ∂P = 0 := le_antisymm hle (integral_nonneg (hY n).2)
    have hae : Y n =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg (hY n).2 (hY n).1.2).mp h0
    have := hLI _ (hY n) 0 (zero_mem P) (sameLaw_of_ae P hae)
    have := hYρ n
    rw [h0, mul_zero, ‹ρ (Y n) = ρ 0›, rho_zero P ρ hA] at this
    exact lt_irrefl _ this
  set c : ℕ → ℝ := fun n => 1 / (2 ^ n * ∫ ω, Y n ω ∂P) with hc
  have hcpos : ∀ n, 0 < c n := fun n => by have := hEpos n; positivity
  set Z : ℕ → Ω → ℝ := fun n => c n • Y n with hZdef
  have hZ : ∀ n, Z n ∈ L1Plus P := fun n => smul_mem P (hY n) _ (hcpos n).le
  have hZint : ∀ n, ∫ ω, Z n ω ∂P = (1/2) ^ n := by
    intro n
    simp only [hZdef, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, hc]
    have := (hEpos n).ne'
    field_simp
    rw [← mul_pow]; norm_num
  have hZρ : ∀ n, (2:ℝ) ^ n < ρ (Z n) := by
    intro n
    rw [hZdef, rho_smul P ρ hM hA (hY n) _ (hcpos n).le]
    have h1 := mul_lt_mul_of_pos_left (hYρ n) (hcpos n)
    have h2 : c n * ((4:ℝ) ^ n * ∫ ω, Y n ω ∂P) = 2 ^ n := by
      rw [hc]
      have := (hEpos n).ne'
      rw [show (4:ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
      field_simp
    linarith
  set f : ℕ → Ω → ENNReal := fun n ω => ENNReal.ofReal (Z n ω) with hf
  have hfm : ∀ n, Measurable (f n) := fun n => ENNReal.measurable_ofReal.comp (hZ n).1.1
  have hlint : ∫⁻ ω, ∑' n, f n ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun n => (hfm n).aemeasurable]
    have : ∀ n, ∫⁻ ω, f n ω ∂P = (2⁻¹ : ENNReal) ^ n := by
      intro n
      simp only [hf]
      rw [← ofReal_integral_eq_lintegral_ofReal (hZ n).1.2 (Eventually.of_forall (hZ n).2),
        hZint n, ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos]
      simp
    simp only [this]
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]; simp
  set D : Set Ω := {ω | ∑' n, f n ω = ⊤} with hDdef
  have hDm : MeasurableSet D :=
    measurableSet_eq_fun (Measurable.ennreal_tsum hfm) measurable_const
  have hD0 : P D = 0 := by
    have := ae_lt_top (Measurable.ennreal_tsum hfm) hlint
    rw [ae_iff] at this
    have e : {a | ¬∑' n, f n a < ⊤} = D := by ext ω; simp [hDdef]
    rwa [e] at this
  set Z' : ℕ → Ω → ℝ := fun n => Dᶜ.indicator (Z n) with hZ'def
  have hZ' : ∀ n, Z' n ∈ L1Plus P := fun n =>
    ⟨⟨(hZ n).1.1.indicator hDm.compl, (hZ n).1.2.indicator hDm.compl⟩,
      fun ω => Set.indicator_nonneg (fun ω _ => (hZ n).2 ω) ω⟩
  have hZ'ae : ∀ n, Z' n =ᵐ[P] Z n := by
    intro n
    have : ∀ᵐ ω ∂P, ω ∈ Dᶜ := compl_mem_ae_iff.mpr hD0
    filter_upwards [this] with ω hω
    simp only [hZ'def, Set.indicator_of_mem hω]
  have hZ'ρ : ∀ n, ρ (Z' n) = ρ (Z n) := fun n =>
    hLI _ (hZ' n) _ (hZ n) (sameLaw_of_ae P (hZ'ae n))
  set W : Ω → ℝ := fun ω => (∑' n, ENNReal.ofReal (Z' n ω)).toReal with hWdef
  have hWm : Measurable W := ENNReal.measurable_toReal.comp
    (Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp (hZ' n).1.1)
  have hWint : Integrable W P := by
    apply integrable_toReal_of_lintegral_ne_top
      (Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp (hZ' n).1.1).aemeasurable
    refine ne_top_of_le_ne_top hlint (lintegral_mono fun ω => ENNReal.tsum_le_tsum fun n => ?_)
    apply ENNReal.ofReal_le_ofReal
    simp only [hZ'def]
    exact Set.indicator_le_self' (fun ω _ => (hZ n).2 ω) ω
  have hW : W ∈ L1Plus P := ⟨⟨hWm, hWint⟩, fun ω => ENNReal.toReal_nonneg⟩
  have hpartial : ∀ N : ℕ, ∀ ω, (∑ n ∈ Finset.range N, Z' n) ω ≤ W ω := by
    intro N ω
    rw [Finset.sum_apply]
    by_cases hω : ω ∈ D
    · have : ∀ n, Z' n ω = 0 := fun n => by
        simp only [hZ'def]; exact Set.indicator_of_notMem (show ω ∉ Dᶜ from fun h => h hω) _
      simp only [this, Finset.sum_const_zero]
      exact ENNReal.toReal_nonneg
    · have hval : ∀ n, Z' n ω = Z n ω := fun n => by
        simp only [hZ'def]; exact Set.indicator_of_mem hω _
      have hfin : ∑' n, f n ω ≠ ⊤ := hω
      simp only [hWdef, hval]
      have : ∑ n ∈ Finset.range N, Z n ω = (∑ n ∈ Finset.range N, f n ω).toReal := by
        rw [ENNReal.toReal_sum (fun n _ => ENNReal.ofReal_ne_top)]
        apply Finset.sum_congr rfl
        intro n _
        exact (ENNReal.toReal_ofReal ((hZ n).2 ω)).symm
      rw [this]
      exact ENNReal.toReal_mono hfin (ENNReal.sum_le_tsum _)
  obtain ⟨N, hN⟩ := exists_nat_gt (ρ W)
  have h1 := hM _ (sum_mem P _ _ fun n _ => hZ' n) _ hW (hpartial N)
  rw [rho_sum P ρ hA _ _ fun n _ => hZ' n] at h1
  have h2 : (N:ℝ) ≤ ∑ n ∈ Finset.range N, ρ (Z' n) := by
    have : ∑ n ∈ Finset.range N, (1:ℝ) ≤ ∑ n ∈ Finset.range N, ρ (Z' n) := by
      apply Finset.sum_le_sum
      intro n _
      rw [hZ'ρ]
      have := hZρ n
      have : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      linarith
    simpa using this
  linarith

include hP hM hA hLI in
theorem a1_forward : ∀ X ∈ L1Plus P, ρ X = ρ (I Set.univ) * ∫ ω, X ω ∂P := by
  set lam := ρ (I Set.univ) with hlam
  obtain ⟨C, hC⟩ := rho_bound P ρ hM hA hLI
  intro X hX
  set m : ℕ → Ω → ℝ := fun n ω => min (X ω) n with hm
  set r : ℕ → Ω → ℝ := fun n ω => max (X ω - n) 0 with hr
  have hmmem : ∀ n, m n ∈ L1Plus P := fun n =>
    ⟨⟨hX.1.1.min measurable_const, hX.1.2.inf (integrable_const _)⟩,
      fun ω => le_min (hX.2 ω) (Nat.cast_nonneg n)⟩
  have hrmem : ∀ n, r n ∈ L1Plus P := by
    intro n
    refine ⟨⟨(hX.1.1.sub measurable_const).max measurable_const, ?_⟩, fun ω => le_max_right _ _⟩
    refine Integrable.mono' hX.1.2 ((hX.1.1.sub measurable_const).max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    simp only [hr, Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    have := hX.2 ω
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    exact max_le (by linarith) (hX.2 ω)
  have hsplit : ∀ n, X = m n + r n := by
    intro n; funext ω
    simp only [hm, hr, Pi.add_apply]
    rcases le_total (X ω) n with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have hρ : ∀ n, ρ X = lam * ∫ ω, m n ω ∂P + ρ (r n) := by
    intro n
    conv_lhs => rw [hsplit n]
    rw [hA _ (hmmem n) _ (hrmem n), rho_bounded P hP ρ hM hA hLI (m n) (hmmem n) n
      (fun ω => min_le_right _ _)]
  have hint : ∀ n, ∫ ω, r n ω ∂P = ∫ ω, X ω ∂P - ∫ ω, m n ω ∂P := by
    intro n
    have := congrArg (fun f => ∫ ω, f ω ∂P) (hsplit n)
    simp only [Pi.add_apply] at this
    rw [integral_add (hmmem n).1.2 (hrmem n).1.2] at this
    linarith
  have hlim : Tendsto (fun n : ℕ => ∫ ω, m n ω ∂P) atTop (𝓝 (∫ ω, X ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence X (fun n => (hmmem n).1.1.aestronglyMeasurable)
      hX.1.2
    · intro n
      refine Eventually.of_forall fun ω => ?_
      simp only [hm, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_min (hX.2 ω) (Nat.cast_nonneg n))]
      exact min_le_left _ _
    · refine Eventually.of_forall fun ω => ?_
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ⌈X ω⌉₊] with n hn
      simp only [hm]
      rw [min_eq_left]
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hlo : ∀ n, lam * ∫ ω, m n ω ∂P ≤ ρ X := fun n => by
    rw [hρ n]; linarith [rho_nonneg P ρ hM hA (hrmem n)]
  have hhi : ∀ n, ρ X ≤ lam * ∫ ω, m n ω ∂P + C * (∫ ω, X ω ∂P - ∫ ω, m n ω ∂P) := fun n => by
    rw [hρ n, ← hint n]; linarith [hC _ (hrmem n)]
  have t1 : Tendsto (fun n : ℕ => lam * ∫ ω, m n ω ∂P) atTop (𝓝 (lam * ∫ ω, X ω ∂P)) :=
    hlim.const_mul lam
  have t2 : Tendsto (fun n : ℕ => lam * ∫ ω, m n ω ∂P + C * (∫ ω, X ω ∂P - ∫ ω, m n ω ∂P))
      atTop (𝓝 (lam * ∫ ω, X ω ∂P + C * (∫ ω, X ω ∂P - ∫ ω, X ω ∂P))) :=
    t1.add ((tendsto_const_nhds.sub hlim).const_mul C)
  rw [sub_self, mul_zero, add_zero] at t2
  exact le_antisymm (ge_of_tendsto' t2 hhi) (le_of_tendsto' t1 hlo)

end

theorem lemmaA1 (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (ρ : (Ω → ℝ) → ℝ) :
    (AxiomM (L1Plus P) ρ ∧ IsAdditiveOn (L1Plus P) ρ ∧ AxiomLI P (L1Plus P) ρ) ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ X ∈ L1Plus P, ρ X = c * ∫ ω, X ω ∂P := by
  constructor
  · rintro ⟨hM, hA, hLI⟩
    exact ⟨ρ (I Set.univ), rho_nonneg P ρ hM hA (I_mem P _ MeasurableSet.univ),
      a1_forward P hP ρ hM hA hLI⟩
  · rintro ⟨c, hc, hρ⟩
    refine ⟨?_, ?_, ?_⟩
    · intro X hX Y hY hXY
      rw [hρ X hX, hρ Y hY]
      exact mul_le_mul_of_nonneg_left (integral_mono hX.1.2 hY.1.2 hXY) hc
    · intro X hX Y hY
      rw [hρ X hX, hρ Y hY, hρ _ (add_mem P hX hY)]
      simp only [Pi.add_apply]
      rw [integral_add hX.1.2 hY.1.2]; ring
    · intro X hX Y hY hXY
      rw [hρ X hX, hρ Y hY, integral_eq_of_sameLaw P X Y hX.1.1 hY.1.1 hXY]

end ESAxA1Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (ρ : (Ω → ℝ) → ℝ) :
    (ESAxioms.Characterization.AxiomM (ESAxioms.Characterization.L1Plus P) ρ ∧
      ESAxioms.Characterization.IsAdditiveOn (ESAxioms.Characterization.L1Plus P) ρ ∧
      ESAxioms.Characterization.AxiomLI P (ESAxioms.Characterization.L1Plus P) ρ) ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ X ∈ ESAxioms.Characterization.L1Plus P, ρ X = c * ∫ ω, X ω ∂P :=
  ESAxA1Aux.lemmaA1 P hP ρ
