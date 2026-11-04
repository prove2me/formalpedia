-- Prove2me | solution 1 for CompoundSMM.Conv.theorem_5
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:59:32.386207+00:00
-- url     : https://prove2.me/submissions/8e41a84b-8c8c-4515-9c76-b1809afa1488

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology CompoundSMM.Conv

universe u v

namespace SMM5Counter

noncomputable abbrev e1 : E 1 := EuclideanSpace.single 0 1

lemma e1_zero : e1 0 = 1 := by simp [e1]

lemma norm_E1 (v : E 1) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

lemma ext_E1 {v w : E 1} (h : v 0 = w 0) : v = w := by
  ext i; rw [Subsingleton.elim i 0]; exact h

noncomputable def Mfun (x' : E 1) : ℝ :=
  max 0 (1 / (2 * (x' 0) ^ 2) + 1 / (2 * |x' 0|) - 1 / 2)

lemma Mfun_nonneg (x' : E 1) : 0 ≤ Mfun x' := le_max_left _ _

noncomputable def gS (x' : E 1) (y : E 1) : E 1 := y + (Mfun x' * (y 0 - x' 0) ^ 2) • e1

lemma gS_apply (x' y : E 1) : gS x' y 0 = y 0 + Mfun x' * (y 0 - x' 0) ^ 2 := by
  simp [gS, e1]

lemma Mfun_of_zero {x' : E 1} (h : x' 0 = 0) : Mfun x' = 0 := by
  simp [Mfun, h]

lemma gS_of_zero {x' : E 1} (h : x' 0 = 0) (y : E 1) : gS x' y = y := by
  simp [gS, Mfun_of_zero h]

def XX : Set (E 1) := Metric.closedBall 0 1

lemma mem_XX (y : E 1) : y ∈ XX ↔ |y 0| ≤ 1 := by
  simp [XX, norm_E1]

noncomputable def P : CompoundSP.{u} 1 1 0 1 PUnit.{u+1} where
  μ := Measure.dirac PUnit.unit
  isProb := inferInstance
  X := XX
  G := fun x _ => x
  F := fun _ _ => 0
  φ := fun a _ => a
  ψ := fun u => u 0
  dims := by norm_num
  carathG := ⟨fun _ => continuousOn_id, fun _ _ => integrable_const _⟩
  carathF := ⟨fun _ => continuousOn_const, fun _ _ => integrable_const _⟩
  contφ := continuous_fst
  contψ := by fun_prop

instance instPprob : IsProbabilityMeasure P.{u}.μ := P.isProb

def 𝒢 : E 1 → PUnit.{u+1} → Set (E 1 → E 1) := fun x' _ => {gS x'}
def ℱ : E 1 → PUnit.{u+1} → Set (E 1 → E 0) := fun _ _ => {fun _ => 0}

lemma hA1 : A1 P.{u} := by
  refine ⟨⟨0, by simp [P, XX]⟩, convex_closedBall _ _, isCompact_closedBall _ _⟩

lemma hA2 : A2 P.{u} 1 1 := by
  refine ⟨zero_le_one, zero_le_one, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v h; exact h 0
  · intro a a' b b' h _ j; exact h j
  · intro u v
    simp only [P, one_mul]
    have := PiLp.norm_apply_le (u - v) 0
    simpa [Real.norm_eq_abs] using this
  · intro a a' b b'
    simp only [P, one_mul]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg ‖b - b'‖]
  · refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
    simp [P]
  · intro j
    refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
    simp [P]

lemma hA4 : A4 P.{u} 0 0 := by
  refine ⟨le_rfl, le_rfl, fun x _ => ⟨by simp only [P]; exact memLp_const _, by simp only [P]; exact memLp_const _, ?_, ?_⟩⟩
  · simp [P]
  · simp [P]


lemma gS_self (x' : E 1) : gS x' x' = x' := by simp [gS]

lemma gS_convex (x' : E 1) (i : Fin 1) : ConvexOn ℝ XX (fun x => gS x' x i) := by
  rw [Subsingleton.elim i 0]
  refine ⟨convex_closedBall _ _, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [gS_apply, smul_eq_mul, PiLp.add_apply, PiLp.smul_apply]
  have hM := Mfun_nonneg x'
  have hb' : b = 1 - a := by linarith
  subst hb'
  have : 0 ≤ Mfun x' * (a * (1 - a)) * (x 0 - y 0) ^ 2 :=
    mul_nonneg (mul_nonneg hM (mul_nonneg ha hb)) (sq_nonneg _)
  nlinarith [this]

/-- continuity of `Mfun` away from `0`. -/
lemma Mfun_continuousAt {y : E 1} (hy : y 0 ≠ 0) : ContinuousAt Mfun y := by
  unfold Mfun
  have h0 : ContinuousAt (fun x : E 1 => x 0) y := by fun_prop
  have h1 : ContinuousAt (fun x : E 1 => 1 / (2 * (x 0) ^ 2)) y :=
    continuousAt_const.div (by fun_prop) (by positivity)
  have h2 : ContinuousAt (fun x : E 1 => 1 / (2 * |x 0|)) y :=
    continuousAt_const.div (by fun_prop) (by positivity)
  exact continuousAt_const.max ((h1.add h2).sub continuousAt_const)

lemma osc (xs : ℕ → E 1) (xinf : E 1) (hxs : ∀ ν, xs ν ∈ XX)
    (hlim : Tendsto xs atTop (𝓝 xinf)) (Mb : ℝ)
    (hb : ∀ ν, ∀ x ∈ XX, ‖gS (xs ν) x‖ ≤ Mb) :
    ∃ K : Set ℕ, K.Infinite ∧ ∀ x ∈ XX, ∀ ε > 0, ∃ νbar : ℕ, ∀ ν ∈ K, νbar ≤ ν →
      ‖gS (xs ν) x - gS xinf x‖ ≤ ε * 1 := by
  have hc : Tendsto (fun ν => xs ν 0) atTop (𝓝 (xinf 0)) :=
    ((PiLp.continuous_apply 2 _ 0).tendsto xinf).comp hlim
  by_cases hy : xinf 0 ≠ 0
  · refine ⟨Set.univ, Set.infinite_univ, fun x _ ε hε => ?_⟩
    have hM : Tendsto (fun ν => Mfun (xs ν)) atTop (𝓝 (Mfun xinf)) :=
      (Mfun_continuousAt hy).tendsto.comp hlim
    have hT : Tendsto (fun ν => gS (xs ν) x) atTop (𝓝 (gS xinf x)) := by
      unfold gS
      refine tendsto_const_nhds.add (Tendsto.smul_const ?_ _)
      exact hM.mul ((tendsto_const_nhds.sub hc).pow 2)
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hT ε hε
    refine ⟨N0, fun ν _ hν => ?_⟩
    rw [mul_one, ← dist_eq_norm]; exact (hN0 ν hν).le
  push Not at hy
  by_cases hev : ∃ ν0, ∀ ν ≥ ν0, xs ν 0 = 0
  · obtain ⟨ν0, hν0⟩ := hev
    refine ⟨Set.Ici ν0, Set.Ici_infinite ν0, fun x _ ε hε => ⟨ν0, fun ν hν _ => ?_⟩⟩
    rw [gS_of_zero (hν0 ν hν), gS_of_zero hy, sub_self, norm_zero]; positivity
  exfalso
  push Not at hev
  have hMb : 0 ≤ Mb := le_trans (norm_nonneg _) (hb 0 (xs 0) (hxs 0))
  have hδ : (0 : ℝ) < 1 / (2 * Mb + 3) := by positivity
  rw [hy] at hc
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hc _ hδ
  obtain ⟨ν, hνN, hν0⟩ := hev N0
  have hsmall := hN0 ν hνN
  rw [Real.dist_eq, sub_zero] at hsmall
  set a := xs ν 0 with ha
  have hapos : 0 < |a| := abs_pos.mpr hν0
  have hδ1 : 1 / (2 * Mb + 3) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have ha1 : |a| < 1 := lt_of_lt_of_le hsmall hδ1
  -- test point
  set y : E 1 := if 0 < a then -e1 else e1 with hydef
  have hy0 : y 0 = if 0 < a then -1 else 1 := by
    rw [hydef]; split_ifs <;> simp [e1]
  have hyX : y ∈ XX := by
    rw [mem_XX, hy0]; split_ifs <;> simp
  have hdist : 1 ≤ (y 0 - a) ^ 2 := by
    rw [hy0]
    split_ifs with h
    · nlinarith
    · push Not at h; nlinarith
  have hbound := hb ν y hyX
  have hnorm : gS (xs ν) y 0 ≤ ‖gS (xs ν) y‖ := by
    rw [norm_E1]; exact le_abs_self _
  rw [gS_apply, ← ha] at hnorm
  have hM : 1 / (2 * a ^ 2) - 1 / 2 ≤ Mfun (xs ν) := by
    unfold Mfun; rw [← ha]
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ 1 / (2 * |a|) := by positivity
    linarith
  have hy0b : -1 ≤ y 0 := by rw [hy0]; split_ifs <;> norm_num
  have ha2pos : 0 < a ^ 2 := by positivity
  have ha2 : a ^ 2 < 1 / (2 * Mb + 3) := by
    have : a ^ 2 = |a| * |a| := by rw [← sq_abs]; ring
    rw [this]
    calc |a| * |a| ≤ |a| * 1 := by gcongr
      _ < 1 / (2 * Mb + 3) := by linarith
  have hinv : 2 * Mb + 3 < 1 / a ^ 2 := by
    rw [lt_div_iff₀ ha2pos]
    rw [lt_div_iff₀ (by positivity)] at ha2
    linarith
  have hM2 : Mb + 1 < Mfun (xs ν) := by
    have : 1 / (2 * a ^ 2) = (1 / a ^ 2) / 2 := by field_simp
    rw [this] at hM
    linarith
  have hMnn := Mfun_nonneg (xs ν)
  have : Mfun (xs ν) ≤ Mfun (xs ν) * (y 0 - a) ^ 2 := by
    nlinarith
  linarith

lemma hA3G : SurrogateFamily P.{u}.X P.{u}.μ P.{u}.G 𝒢.{u} := by
  refine ⟨fun _ _ _ => Set.singleton_nonempty _, ?_, ?_, ?_, ?_⟩
  · intro x' _ ξ g hg
    rw [Set.mem_singleton_iff.mp hg]; exact gS_self x'
  · intro x' _ ξ g hg x _ i
    rw [Set.mem_singleton_iff.mp hg, Subsingleton.elim i 0, gS_apply]
    have := mul_nonneg (Mfun_nonneg x') (sq_nonneg (x 0 - x' 0))
    simp only [P]; linarith
  · intro x' _ ξ g hg i
    rw [Set.mem_singleton_iff.mp hg]; exact gS_convex x' i
  · refine ⟨fun _ => 1, fun _ => zero_le_one, integrable_const _, ?_⟩
    intro xs xinf hxs hlim gs hgs hbd
    have hgs' : ∀ ν, gs ν PUnit.unit = gS (xs ν) := fun ν => Set.mem_singleton_iff.mp (hgs ν _)
    obtain ⟨Mb, hMb⟩ := hbd PUnit.unit
    obtain ⟨K, hK, hKp⟩ := osc xs xinf hxs hlim Mb (fun ν x hx => by
      rw [← hgs' ν]; exact hMb ν x hx)
    refine ⟨fun _ => gS xinf, fun _ => rfl, K, hK, fun x hx ε hε => ?_⟩
    obtain ⟨νbar, h⟩ := hKp x hx ε hε
    refine ⟨νbar, fun ν hν hle ξ => ?_⟩
    rw [Subsingleton.elim ξ PUnit.unit, hgs' ν]
    exact h ν hν hle

lemma hA3F : SurrogateFamily P.{u}.X P.{u}.μ P.{u}.F ℱ.{u} := by
  refine ⟨fun _ _ _ => Set.singleton_nonempty _, ?_, ?_, ?_, ?_⟩
  · intro x' _ ξ g hg
    rw [Set.mem_singleton_iff.mp hg]; rfl
  · intro x' _ ξ g hg x _ i
    exact i.elim0
  · intro x' _ ξ g hg i
    rw [Set.mem_singleton_iff.mp hg]; exact convexOn_const _ (convex_closedBall _ _)
  · refine ⟨fun _ => 1, fun _ => zero_le_one, integrable_const _, ?_⟩
    intro xs xinf hxs hlim gs hgs hbd
    refine ⟨fun _ => fun _ => 0, fun _ => rfl, Set.univ, Set.infinite_univ,
      fun x _ ε hε => ⟨0, fun ν _ _ ξ => ?_⟩⟩
    rw [Set.mem_singleton_iff.mp (hgs ν ξ)]
    simp; positivity


noncomputable def xs (ν : ℕ) : E 1 := if ν = 0 then e1 else ((ν : ℝ)⁻¹) • e1

lemma xs_apply {ν : ℕ} (h : ν ≠ 0) : xs ν 0 = (ν : ℝ)⁻¹ := by
  simp [xs, h, e1]

lemma xs_mem (ν : ℕ) : xs ν ∈ XX := by
  rw [mem_XX]
  by_cases h : ν = 0
  · simp [xs, h, e1]
  · rw [xs_apply h, abs_of_nonneg (by positivity)]
    apply inv_le_one_of_one_le₀
    exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h)

lemma xs_tendsto : Tendsto xs atTop (𝓝 0) := by
  have h : Tendsto (fun ν : ℕ => ((ν : ℝ)⁻¹) • e1) atTop (𝓝 ((0 : ℝ) • e1)) :=
    tendsto_inv_atTop_nhds_zero_nat.smul_const _
  rw [zero_smul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with ν hν
  simp [xs, hν]

lemma VN_eq (N : ℕ) (hN : 0 < N) (g : E 1 → E 1) (fs : ℕ → E 1 → E 0) (y : E 1) :
    VN P.{u} N (fun _ => g) fs y = g y 0 := by
  simp only [VN, P, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

lemma step (ν : ℕ) (hν : 1 ≤ ν) (y : E 1) :
    gS (xs ν) (xs (ν + 1)) 0 + ‖xs (ν + 1) - xs ν‖ ^ 2 / (2 * 1)
      ≤ gS (xs ν) y 0 + ‖y - xs ν‖ ^ 2 / (2 * 1) := by
  have hν0 : ν ≠ 0 := by omega
  rw [gS_apply, gS_apply, norm_E1, norm_E1, sq_abs, sq_abs]
  simp only [PiLp.sub_apply]
  rw [xs_apply hν0, xs_apply (by omega : ν + 1 ≠ 0)]
  have hνr : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hM : Mfun (xs ν) = ((ν : ℝ) ^ 2 + ν - 1) / 2 := by
    unfold Mfun
    rw [xs_apply hν0, abs_of_nonneg (by positivity)]
    have e : 1 / (2 * ((ν : ℝ)⁻¹) ^ 2) + 1 / (2 * (ν : ℝ)⁻¹) - 1 / 2
        = ((ν : ℝ) ^ 2 + ν - 1) / 2 := by
      field_simp
    rw [e]
    apply max_eq_right
    have : (0 : ℝ) ≤ (ν : ℝ) ^ 2 + ν - 1 := by nlinarith
    positivity
  rw [hM]
  push_cast
  set t := y 0
  have hpos : (0 : ℝ) < ν := by linarith
  have key : t + ((ν : ℝ) ^ 2 + ν - 1) / 2 * (t - (ν : ℝ)⁻¹) ^ 2 + (t - (ν : ℝ)⁻¹) ^ 2 / (2 * 1)
      - (((ν : ℝ) + 1)⁻¹ + ((ν : ℝ) ^ 2 + ν - 1) / 2 * (((ν : ℝ) + 1)⁻¹ - (ν : ℝ)⁻¹) ^ 2
        + (((ν : ℝ) + 1)⁻¹ - (ν : ℝ)⁻¹) ^ 2 / (2 * 1))
      = (ν : ℝ) * (ν + 1) / 2 * (t - ((ν : ℝ) + 1)⁻¹) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ (ν : ℝ) * (ν + 1) / 2 * (t - ((ν : ℝ) + 1)⁻¹) ^ 2 := by positivity
  linarith

lemma hNcond : SampleSizeCond (fun ν => ν ^ 2) := by
  refine ⟨3, by norm_num, 1 / 2, 1, 2, by norm_num, by norm_num, by norm_num, fun ν hν => ?_⟩
  have hν1 : 1 ≤ ν := by omega
  have hc : (((ν - 1) ^ 2 : ℕ) : ℝ) = ((ν : ℝ) - 1) ^ 2 := by
    push_cast [Nat.cast_sub hν1]; ring
  simp only
  rw [hc]
  have hνr : (4 : ℝ) ≤ ν := by exact_mod_cast hν
  have hr : (ν : ℝ) ^ (1 + 2 * (1 / 2 : ℝ)) = (ν : ℝ) ^ 2 := by
    rw [show (1 + 2 * (1 / 2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hr]
  push_cast
  constructor
  · apply max_le <;> nlinarith
  · have hpos : 0 < 1 - 2 / (ν : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    rw [le_div_iff₀ hpos]
    have : (ν : ℝ) ^ 2 * (1 - 2 / ν) = (ν : ℝ) ^ 2 - 2 * ν := by field_simp
    rw [this]; nlinarith

lemma iid : IIDSamples.{u, v} (Measure.dirac PUnit.unit) P.{u}.μ
    (fun _ _ => PUnit.unit) (fun _ _ => PUnit.unit) := by
  refine ⟨fun _ => measurable_const, fun _ => measurable_const, ?_, ?_, ?_⟩
  · rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets _
    by_cases hall : ∀ i ∈ S, PUnit.unit ∈ sets i
    · have h1 : ∀ i ∈ S, (Measure.dirac PUnit.unit : Measure PUnit.{v+1})
          ((Sum.elim (fun _ _ => PUnit.unit) (fun _ _ => PUnit.unit) i : PUnit.{v+1} → PUnit.{u+1}) ⁻¹' sets i) = 1 := by
        intro i hi
        rw [Measure.dirac_apply]
        rw [Set.indicator_of_mem]
        · rfl
        · simp only [Set.mem_preimage]
          convert hall i hi
      rw [Finset.prod_congr rfl h1, Finset.prod_const_one, Measure.dirac_apply,
        Set.indicator_of_mem]
      · rfl
      · simp only [Set.mem_iInter, Set.mem_preimage]
        intro i hi
        convert hall i hi
    · push Not at hall
      obtain ⟨i0, hi0, hn⟩ := hall
      have h0 : (Measure.dirac PUnit.unit : Measure PUnit.{v+1})
          ((Sum.elim (fun _ _ => PUnit.unit) (fun _ _ => PUnit.unit) i0 : PUnit.{v+1} → PUnit.{u+1}) ⁻¹' sets i0) = 0 := by
        rw [Measure.dirac_apply, Set.indicator_of_notMem]
        simp only [Set.mem_preimage]
        convert hn
      rw [Finset.prod_eq_zero hi0 h0, Measure.dirac_apply, Set.indicator_of_notMem]
      simp only [Set.mem_iInter, Set.mem_preimage, not_forall]
      exact ⟨i0, hi0, by convert hn⟩
  · intro t; simp [P, Measure.map_const]
  · intro s; simp [P, Measure.map_const]

noncomputable def R : SMMRun P.{u} 𝒢.{u} ℱ.{u} 1 PUnit.{v+1} where
  Pr := Measure.dirac PUnit.unit
  isProb := inferInstance
  ξs := fun _ _ => PUnit.unit
  ηs := fun _ _ => PUnit.unit
  iid := iid
  N := fun ν => ν ^ 2
  hN := ⟨by simp, fun a b h => Nat.pow_le_pow_left h 2, fun ν h => by positivity⟩
  gsel := fun _ x' _ => gS x'
  fsel := fun _ _ _ => fun _ => 0
  hsel := fun _ _ _ _ => ⟨rfl, rfl⟩
  hselMeas := fun _ y => by
    refine ⟨?_, measurable_const⟩
    unfold gS Mfun
    fun_prop
  x0 := e1
  hx0 := by
    have h := xs_mem 0
    simp only [xs, if_pos rfl] at h
    exact h
  x := fun ν _ => xs ν
  hx01 := fun _ => ⟨by simp [xs], by simp [xs]⟩
  hmeas := fun _ => measurable_const
  hstep := fun ν hν ω => ⟨xs_mem (ν + 1), fun y _ => by
    have hN : 0 < ν ^ 2 := by positivity
    rw [VN_eq _ hN, VN_eq _ hN]
    exact step ν hν y⟩


lemma bcf_conv {k : ℕ} (S : Set (BoundedContinuousFunction (↥(P.{u}.X)) (E k)))
    (h : S.Subsingleton) : IsCompact S ∧ Convex ℝ S := by
  refine ⟨h.isCompact, ?_⟩
  intro x hx y hy a b _ _ hab
  rw [h hy hx]
  have : a • x + b • x = x := by
    ext z : 1
    simp only [BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul,
      Pi.add_apply, Pi.smul_apply]
    rw [← add_smul, hab, one_smul]
  rw [this]; exact hx

lemma Einf𝒢 : EinfFamily P.{u}.X P.{u}.μ 𝒢.{u} 0 := by
  have hg0 : gS (0 : E 1) = id := funext fun y => gS_of_zero (by simp) y
  refine ⟨?_, fun _ => 1, integrable_const _, ?_⟩
  · change ∀ᵐ ξ ∂(Measure.dirac PUnit.unit), _
    rw [ae_dirac_eq, Filter.eventually_pure]
    have hsub : Set.Subsingleton {h : BoundedContinuousFunction (↥(P.{u}.X)) (E 1) |
        ∃ g ∈ 𝒢.{u} 0 PUnit.unit, ∀ y : ↥(P.{u}.X), h y = g y} := by
      rintro h1 ⟨g1, hg1, e1'⟩ h2 ⟨g2, hg2, e2'⟩
      ext y : 1
      rw [e1', e2', Set.mem_singleton_iff.mp hg1, Set.mem_singleton_iff.mp hg2]
    refine ⟨fun g hg => ?_, (bcf_conv _ hsub).1, (bcf_conv _ hsub).2⟩
    rw [Set.mem_singleton_iff.mp hg, hg0]; exact continuousOn_id
  · change ∀ᵐ ξ ∂(Measure.dirac PUnit.unit), _
    rw [ae_dirac_eq, Filter.eventually_pure]
    intro g hg y hy
    rw [Set.mem_singleton_iff.mp hg, hg0]
    simpa [P, XX] using hy

lemma Einfℱ : EinfFamily P.{u}.X P.{u}.μ ℱ.{u} 0 := by
  refine ⟨?_, fun _ => 1, integrable_const _, ?_⟩
  · change ∀ᵐ ξ ∂(Measure.dirac PUnit.unit), _
    rw [ae_dirac_eq, Filter.eventually_pure]
    have hsub : Set.Subsingleton {h : BoundedContinuousFunction (↥(P.{u}.X)) (E 0) |
        ∃ g ∈ ℱ.{u} 0 PUnit.unit, ∀ y : ↥(P.{u}.X), h y = g y} := by
      rintro h1 ⟨g1, hg1, e1'⟩ h2 ⟨g2, hg2, e2'⟩
      ext y : 1
      rw [e1', e2', Set.mem_singleton_iff.mp hg1, Set.mem_singleton_iff.mp hg2]
    refine ⟨fun g hg => ?_, (bcf_conv _ hsub).1, (bcf_conv _ hsub).2⟩
    rw [Set.mem_singleton_iff.mp hg]; exact continuousOn_const
  · change ∀ᵐ ξ ∂(Measure.dirac PUnit.unit), _
    rw [ae_dirac_eq, Filter.eventually_pure]
    intro g hg y hy
    rw [Set.mem_singleton_iff.mp hg]
    simp

lemma not_min (g : PUnit.{u+1} → E 1 → E 1) (f : PUnit.{u+1} → E 1 → E 0)
    (hg : g PUnit.unit = gS 0) : ¬ IsMinOn (Vhat P.{u} g f) P.{u}.X 0 := by
  intro hmin
  have hm1 : (-e1 : E 1) ∈ P.{u}.X := by
    show -e1 ∈ XX
    rw [mem_XX]; simp [e1]
  have := hmin hm1
  simp only [Set.mem_setOf_eq, Vhat, P, integral_dirac, hg] at this
  rw [gS_of_zero (by simp), gS_of_zero (by simp)] at this
  simp [e1] at this
  linarith

end SMM5Counter

open SMM5Counter in
theorem solution : ¬ (∀ {n ℓG ℓF ℓφ : ℕ} {Ξ Ω : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (P : CompoundSP n ℓG ℓF ℓφ Ξ) (𝒢 : E n → Ξ → Set (E n → E ℓG))
    (ℱ : E n → Ξ → Set (E n → E ℓF)) (Lψ Lφ σF σG : ℝ) (hA1 : A1 P) (hA2 : A2 P Lψ Lφ)
    (hA3G : SurrogateFamily P.X P.μ P.G 𝒢) (hA3F : SurrogateFamily P.X P.μ P.F ℱ)
    (hA4 : A4 P σF σG) (ρ : ℝ) (hρ : 0 < ρ) (R : SMMRun P 𝒢 ℱ ρ Ω)
    (hN : SampleSizeCond R.N),
    ∀ᵐ ω ∂(R.Pr), ∀ xinf : E n, MapClusterPt xinf atTop (fun ν => R.x ν ω) →
      EinfFamily P.X P.μ 𝒢 xinf → EinfFamily P.X P.μ ℱ xinf →
      xinf ∈ P.X ∧ ∃ (g : Ξ → E n → E ℓG) (f : Ξ → E n → E ℓF),
        WellDefinedMember P 𝒢 ℱ xinf g f ∧ IsMinOn (Vhat P g f) P.X xinf) := by
  intro h
  have H := h SMM5Counter.P SMM5Counter.𝒢 SMM5Counter.ℱ 1 1 0 0 hA1 hA2 hA3G hA3F hA4 1 one_pos
    SMM5Counter.R hNcond
  simp only [SMM5Counter.R, ae_dirac_eq, Filter.eventually_pure] at H
  obtain ⟨-, g, f, hW, hmin⟩ := H 0 xs_tendsto.mapClusterPt Einf𝒢 Einfℱ
  exact not_min g f (Set.mem_singleton_iff.mp (hW.1 PUnit.unit)) hmin
