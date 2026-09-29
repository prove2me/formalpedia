-- Prove2me | solution 1 for AutomorphicForm.unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c5b2c9e3-7b61-5ff0-b482-9f81650ac987

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Pointwise

noncomputable section

namespace KcSplitTorusOrbitalR4

open AutomorphicForm

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

theorem mem_integers_iff_norm (y : Kv) : y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem coe_integers_eq_closedBall :
    (v.adicCompletionIntegers K : Set Kv) = Metric.closedBall (0 : Kv) 1 := by
  ext y
  rw [SetLike.mem_coe, mem_integers_iff_norm, Metric.mem_closedBall, dist_zero_right]

theorem norm_coe_integer_le_one (x : v.adicCompletionIntegers K) : ‖(x : Kv)‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 x.2

theorem uniformiser_ne_zero {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : (ϖ : Kv) ≠ 0 := by
  intro h
  apply hϖ.ne_zero
  exact_mod_cast h

theorem exists_valued_eq_exp_and_norm_eq {x : Kv} (hx : x ≠ 0) :
    ∃ j : ℤ, Valued.v x = WithZero.exp j ∧ ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ j := by
  have hvx : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation Kv (WithZero (Multiplicative ℤ)))).2 hx
  refine ⟨WithZero.log (Valued.v x), (WithZero.exp_log hvx).symm, ?_⟩
  rw [NumberField.FinitePlace.norm_def v x]
  conv_lhs => rw [← WithZero.exp_log hvx]
  rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  congr 1

theorem valued_uniformiser {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : Kv) = WithZero.exp (-1 : ℤ) := by

  obtain ⟨p, hp⟩ := HeightOneSpectrum.intValuation_exists_uniformizer v
  have hpv : Valued.v ((p : 𝓞 K) : Kv) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, hp]

  set p' : v.adicCompletionIntegers K := algebraMap (𝓞 K) (v.adicCompletionIntegers K) p with hp'
  have hp'v : Valued.v (p' : Kv) = WithZero.exp (-1 : ℤ) := hpv
  have hp'max : p' ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v, hp'v, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    norm_num
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hp'max
  obtain ⟨a, ha⟩ := hp'max
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : Kv) := by
    rw [← hp'v, ← ha]
    push_cast
    rw [map_mul]
    calc Valued.v (a : Kv) * Valued.v (ϖ : Kv) ≤ 1 * Valued.v (ϖ : Kv) :=
          mul_le_mul_of_nonneg_right a.2 zero_le'
      _ = Valued.v (ϖ : Kv) := one_mul _

  have hlt : Valued.v (ϖ : Kv) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have hne : Valued.v (ϖ : Kv) ≠ 0 := (Valuation.ne_zero_iff _).2 (uniformiser_ne_zero K v hϖ)
  refine le_antisymm ?_ hle
  rw [← WithZero.log_le_iff_le_exp hne]
  have h0 : WithZero.log (Valued.v (ϖ : Kv)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hne, WithZero.exp_zero]; exact hlt
  omega

theorem norm_uniformiser {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    ‖(ϖ : Kv)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def v, valued_uniformiser K v hϖ,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  rw [← zpow_neg_one]
  congr 1

private theorem _root_.KcSplitTorusOrbitalR4.one_lt_absNorm : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

p2m_export "KcSplitTorusOrbitalR4" "one_lt_absNorm"
theorem norm_uniformiser_pos {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : 0 < ‖(ϖ : Kv)‖ :=
  norm_pos_iff.2 (uniformiser_ne_zero K v hϖ)

theorem norm_uniformiser_lt_one {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : ‖(ϖ : Kv)‖ < 1 := by
  rw [norm_uniformiser K v hϖ]
  exact inv_lt_one_of_one_lt₀ (one_lt_absNorm K v)

theorem exists_norm_eq_zpow {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {c : Kv} (hc : c ≠ 0) :
    ∃ k : ℤ, ‖c‖ = ‖(ϖ : Kv)‖ ^ k := by
  obtain ⟨j, -, hj⟩ := exists_valued_eq_exp_and_norm_eq K v hc
  refine ⟨-j, ?_⟩
  rw [hj, norm_uniformiser K v hϖ, inv_zpow', neg_neg]

theorem norm_le_zpow_succ_of_lt {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {x : Kv} {n : ℤ}
    (hx : ‖x‖ < ‖(ϖ : Kv)‖ ^ n) : ‖x‖ ≤ ‖(ϖ : Kv)‖ ^ (n + 1) := by
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]; exact zpow_nonneg (norm_nonneg _) _
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow K v hϖ hx0
  rw [hk] at hx ⊢
  have h0 := norm_uniformiser_pos K v hϖ
  have h1 := norm_uniformiser_lt_one K v hϖ
  have hnk : n < k := (zpow_lt_zpow_iff_right_of_lt_one₀ h0 h1).1 hx
  exact zpow_le_zpow_right_of_le_one₀ h0 h1.le (by omega)

theorem natCard_quotient_span_uniformiser {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal := by
  classical

  have e1 : (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ≃
      IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).symm.toEquiv

  set f : 𝓞 K →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    (IsLocalRing.residue (v.adicCompletionIntegers K)).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))
    with hf
  have hfs : Function.Surjective f := NumberField.AdelicHaar.residue_algebraMap_surjective (𝓞 K) K v
  have hker : RingHom.ker f = v.asIdeal := by
    refine (Ideal.IsMaximal.eq_of_le v.isMaximal (RingHom.ker_ne_top f) fun a ha => ?_).symm
    rw [RingHom.mem_ker]
    exact NumberField.AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 K) K v ha
  have e2 : (𝓞 K ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hfs)
  rw [Nat.card_congr e1, ← Nat.card_congr e2.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]

section Balls

def ball (ϖ : v.adicCompletionIntegers K) (n : ℤ) : Set Kv := {u | ‖u‖ ≤ ‖(ϖ : Kv)‖ ^ n}

theorem ball_eq_closedBall (ϖ : v.adicCompletionIntegers K) (n : ℤ) :
    ball K v ϖ n = Metric.closedBall (0 : Kv) (‖(ϖ : Kv)‖ ^ n) := by
  ext u; simp [ball, Metric.mem_closedBall, dist_zero_right]

theorem ball_zero (ϖ : v.adicCompletionIntegers K) : ball K v ϖ 0 = (v.adicCompletionIntegers K : Set Kv) := by
  rw [ball_eq_closedBall, zpow_zero, coe_integers_eq_closedBall]

theorem measurableSet_ball [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] (ϖ : v.adicCompletionIntegers K) (n : ℤ) : MeasurableSet (ball K v ϖ n) := by
  rw [ball_eq_closedBall]; exact measurableSet_closedBall

theorem measure_ball_lt_top [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ϖ : v.adicCompletionIntegers K) (n : ℤ) (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ν (ball K v ϖ n) < ⊤ := by
  rw [ball_eq_closedBall]; exact (isCompact_closedBall _ _).measure_lt_top

theorem mem_ball_iff {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (n : ℤ) (u : Kv) :
    u ∈ ball K v ϖ n ↔ ∃ w : Kv, ‖w‖ ≤ 1 ∧ u = (ϖ : Kv) ^ n * w := by
  have h0 := uniformiser_ne_zero K v hϖ
  have hπn : (ϖ : Kv) ^ n ≠ 0 := zpow_ne_zero n h0
  constructor
  · intro hu
    refine ⟨((ϖ : Kv) ^ n)⁻¹ * u, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hπn, one_mul]⟩
    rw [norm_mul, norm_inv, norm_zpow, ← div_eq_inv_mul, div_le_one (zpow_pos (norm_pos_iff.2 h0) n)]
    exact hu
  · rintro ⟨w, hw, rfl⟩
    show ‖(ϖ : Kv) ^ n * w‖ ≤ ‖(ϖ : Kv)‖ ^ n
    rw [norm_mul, norm_zpow]
    exact mul_le_of_le_one_right (zpow_nonneg (norm_nonneg _) n) hw

theorem measure_ball_eq_card_mul_succ [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (n : ℤ)
    (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ν (ball K v ϖ n) = (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ENNReal) * ν (ball K v ϖ (n + 1)) := by
  classical
  have hπ0 : (ϖ : Kv) ≠ 0 := uniformiser_ne_zero K v hϖ
  have hπ1 : ‖(ϖ : Kv)‖ < 1 := norm_uniformiser_lt_one K v hϖ
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_pos_iff.2 hπ0
  set π : Kv := (ϖ : Kv) with hπ
  haveI : Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) := by
    haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := inferInstance
    exact Finite.of_equiv (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
      (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).toEquiv
  letI : Fintype (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span ({ϖ} : Set (v.adicCompletionIntegers K)))) :=
    Ideal.Quotient.mk_surjective
  set s : v.adicCompletionIntegers K ⧸ Ideal.span {ϖ} → v.adicCompletionIntegers K := Function.surjInv hsurj
    with hs
  have hs_mk : ∀ r, Ideal.Quotient.mk (Ideal.span {ϖ}) (s r) = r := fun r => Function.surjInv_eq hsurj r

  set piece : v.adicCompletionIntegers K ⧸ Ideal.span {ϖ} → Set Kv := fun r =>
    (fun u => -(π ^ n * (s r : Kv)) + u) ⁻¹' ball K v ϖ (n + 1) with hpiece
  have hmem_piece : ∀ r u, u ∈ piece r ↔ ‖u - π ^ n * (s r : Kv)‖ ≤ ‖π‖ ^ (n + 1) := by
    intro r u
    simp only [hpiece, Set.mem_preimage, ball, Set.mem_setOf_eq]
    rw [neg_add_eq_sub]

  have hcong : ∀ a b : v.adicCompletionIntegers K,
      Ideal.Quotient.mk (Ideal.span {ϖ}) a = Ideal.Quotient.mk (Ideal.span {ϖ}) b ↔ ‖(a : Kv) - b‖ ≤ ‖π‖ := by
    intro a b
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      have hc' := congrArg (fun x : v.adicCompletionIntegers K => (x : Kv)) hc
      push_cast at hc'
      rw [← hc', norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_coe_integer_le_one K v c)
    · intro hab
      have hint : ‖π⁻¹ * ((a : Kv) - b)‖ ≤ 1 := by
        rw [norm_mul, norm_inv, ← div_eq_inv_mul, div_le_one hπpos]; exact hab
      refine ⟨⟨_, (mem_integers_iff_norm K v _).2 hint⟩, ?_⟩
      apply Subtype.ext
      push_cast
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul]

  have hcover : (⋃ r, piece r) = ball K v ϖ n := by
    ext u
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨r, hr⟩
      rw [hmem_piece] at hr
      show ‖u‖ ≤ ‖π‖ ^ n
      have hsplit : u = (u - π ^ n * (s r : Kv)) + π ^ n * (s r : Kv) := by ring
      rw [hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr.trans ?_) ?_)
      · exact zpow_le_zpow_right_of_le_one₀ hπpos hπ1.le (by omega)
      · rw [norm_mul, norm_zpow]
        exact mul_le_of_le_one_right (zpow_nonneg (norm_nonneg _) n) (norm_coe_integer_le_one K v _)
    · intro hu
      obtain ⟨w, hw1, rfl⟩ := (mem_ball_iff K v hϖ n _).1 hu
      set w' : v.adicCompletionIntegers K := ⟨w, (mem_integers_iff_norm K v _).2 hw1⟩ with hw'
      refine ⟨Ideal.Quotient.mk (Ideal.span {ϖ}) w', ?_⟩
      rw [hmem_piece, ← mul_sub, norm_mul, norm_zpow, zpow_add_one₀ hπpos.ne']
      refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg (norm_nonneg _) n)
      have : (w : Kv) = (w' : Kv) := rfl
      rw [this]
      exact (hcong _ _).1 (hs_mk _).symm

  have hdisj : Pairwise (Function.onFun Disjoint piece) := by
    intro r r' hrr'
    rw [Function.onFun, Set.disjoint_left]
    intro u hur hur'
    rw [hmem_piece] at hur hur'
    apply hrr'
    have hd : ‖π ^ n * ((s r' : Kv) - s r)‖ ≤ ‖π‖ ^ (n + 1) := by
      have : π ^ n * ((s r' : Kv) - s r) = (u - π ^ n * (s r : Kv)) + -(u - π ^ n * (s r' : Kv)) := by ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hur ?_)
      rw [norm_neg]; exact hur'
    rw [norm_mul, norm_zpow, zpow_add_one₀ hπpos.ne'] at hd
    have hd' : ‖(s r' : Kv) - s r‖ ≤ ‖π‖ := le_of_mul_le_mul_left hd (zpow_pos hπpos n)
    rw [← hs_mk r, ← hs_mk r', eq_comm]
    exact (hcong _ _).2 hd'
  have hmeas : ∀ r, MeasurableSet (piece r) := fun r =>
    (measurable_const_add _) (measurableSet_ball K v ϖ (n + 1))
  have hμ : ∀ r, ν (piece r) = ν (ball K v ϖ (n + 1)) := fun r => measure_preimage_add ν _ _
  rw [← hcover, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem measureReal_ball [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (n : ℤ)
    (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ν.real (ball K v ϖ n) = ‖(ϖ : Kv)‖ ^ n * ν.real (ball K v ϖ 0) := by
  have hq : (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℝ) = ‖(ϖ : Kv)‖⁻¹ := by
    rw [natCard_quotient_span_uniformiser K v hϖ, norm_uniformiser K v hϖ, inv_inv]
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_uniformiser_pos K v hϖ

  have hstep : ∀ m : ℤ, ν.real (ball K v ϖ (m + 1)) = ‖(ϖ : Kv)‖ * ν.real (ball K v ϖ m) := by
    intro m
    have h : ν.real (ball K v ϖ m) = ‖(ϖ : Kv)‖⁻¹ * ν.real (ball K v ϖ (m + 1)) := by
      rw [measureReal_def, measure_ball_eq_card_mul_succ K v hϖ m ν, ENNReal.toReal_mul, ENNReal.toReal_natCast, hq,
        measureReal_def]
    rw [h, ← mul_assoc, mul_inv_cancel₀ hπpos.ne', one_mul]

  induction n using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [hstep, ih, ← mul_assoc, zpow_add_one₀ hπpos.ne', mul_comm (‖(ϖ : Kv)‖ ^ (m : ℤ))]
  | pred m ih =>
    have h := hstep (-(m : ℤ) - 1)
    rw [show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring, ih] at h

    have h' : ν.real (ball K v ϖ (-(m : ℤ) - 1)) = ‖(ϖ : Kv)‖⁻¹ * (‖(ϖ : Kv)‖ ^ (-(m : ℤ)) * ν.real (ball K v ϖ 0)) := by
      rw [h, ← mul_assoc, inv_mul_cancel₀ hπpos.ne', one_mul]
    rw [h', ← mul_assoc]
    congr 1
    rw [show -(m : ℤ) - 1 = -((m : ℤ) + 1) by ring, zpow_neg, zpow_neg, zpow_add_one₀ hπpos.ne', mul_inv,
      mul_comm]

end Balls

section Scaled

theorem setOf_norm_mul_le_eq_ball {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {c : Kv} {k : ℤ}
    (hck : ‖c‖ = ‖(ϖ : Kv)‖ ^ k) (n : ℤ) :
    {u : Kv | ‖c * u‖ ≤ ‖(ϖ : Kv)‖ ^ n} = ball K v ϖ (n - k) := by
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_uniformiser_pos K v hϖ
  ext u
  simp only [Set.mem_setOf_eq, ball, norm_mul, hck]
  rw [zpow_sub₀ hπpos.ne', le_div_iff₀' (zpow_pos hπpos k)]

theorem setOf_norm_mul_eq_eq_diff {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {c : Kv} {k : ℤ}
    (hck : ‖c‖ = ‖(ϖ : Kv)‖ ^ k) (n : ℤ) :
    {u : Kv | ‖c * u‖ = ‖(ϖ : Kv)‖ ^ n} = ball K v ϖ (n - k) \ ball K v ϖ (n + 1 - k) := by
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_uniformiser_pos K v hϖ
  have hπ1 : ‖(ϖ : Kv)‖ < 1 := norm_uniformiser_lt_one K v hϖ
  rw [← setOf_norm_mul_le_eq_ball K v hϖ hck n, ← setOf_norm_mul_le_eq_ball K v hϖ hck (n + 1)]
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_diff, not_le]
  constructor
  · intro h
    refine ⟨h.le, ?_⟩
    rw [h]
    exact zpow_lt_zpow_right_of_lt_one₀ hπpos hπ1 (lt_add_one n)
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (norm_le_zpow_succ_of_lt K v hϖ hlt) (not_le.2 h2)

theorem norm_mul_measureReal_setOf_norm_mul_le [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ)
    {c : Kv} (hc : c ≠ 0) (n : ℤ) (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ‖c‖ * ν.real {u : Kv | ‖c * u‖ ≤ ‖(ϖ : Kv)‖ ^ n} =
      ‖(ϖ : Kv)‖ ^ n * ν.real (v.adicCompletionIntegers K : Set Kv) := by
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_uniformiser_pos K v hϖ
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow K v hϖ hc
  rw [setOf_norm_mul_le_eq_ball K v hϖ hk, measureReal_ball K v hϖ, hk, ← ball_zero K v ϖ, ← mul_assoc]
  congr 1
  rw [zpow_sub₀ hπpos.ne']
  field_simp

theorem norm_mul_measureReal_setOf_norm_mul_eq [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ)
    {c : Kv} (hc : c ≠ 0) (n : ℤ) (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ‖c‖ * ν.real {u : Kv | ‖c * u‖ = ‖(ϖ : Kv)‖ ^ n} =
      ‖(ϖ : Kv)‖ ^ n * (1 - ‖(ϖ : Kv)‖) * ν.real (v.adicCompletionIntegers K : Set Kv) := by
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_uniformiser_pos K v hϖ
  have hπ1 : ‖(ϖ : Kv)‖ < 1 := norm_uniformiser_lt_one K v hϖ
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow K v hϖ hc
  have hsub : ball K v ϖ (n + 1 - k) ⊆ ball K v ϖ (n - k) := fun u hu =>
    le_trans (α := ℝ) hu (zpow_le_zpow_right_of_le_one₀ hπpos hπ1.le (by omega))
  rw [setOf_norm_mul_eq_eq_diff K v hϖ hk, measureReal_diff hsub (measurableSet_ball K v ϖ _)
    (measure_ball_lt_top K v ϖ _ ν).ne, measureReal_ball K v hϖ (n - k), measureReal_ball K v hϖ (n + 1 - k), hk,
    ← ball_zero K v ϖ]
  rw [zpow_sub₀ hπpos.ne', zpow_sub₀ hπpos.ne', zpow_add_one₀ hπpos.ne']
  field_simp

end Scaled

section Fibre

theorem conj_diagonal_coe {a b : Kv} {t : GL (Fin 2) Kv} (ht : (t : M2) = Matrix.diagonal ![a, b]) (u : Kv) :
    (((unipotentGL2 u)⁻¹ * t * unipotentGL2 u : GL (Fin 2) Kv) : M2) = !![a, (a - b) * u; 0, b] := by
  have hinv : (((unipotentGL2 u)⁻¹ : GL (Fin 2) Kv) : M2) = !![1, -u; 0, 1] := rfl
  have hdiag : (Matrix.diagonal ![a, b] : M2) = !![a, 0; 0, b] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [Units.val_mul, Units.val_mul, hinv, unipotentGL2_coe, ht, hdiag, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp; ring
  · simp
  · simp

theorem conj_mem_doubleCoset_iff {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {m₁ m₂ : ℤ} (hm : m₂ ≤ m₁)
    {dl : GL (Fin 2) Kv} (hdl : (dl : M2) = Matrix.diagonal ![(ϖ : Kv) ^ m₁, (ϖ : Kv) ^ m₂])
    {a b : Kv} {t : GL (Fin 2) Kv} (ht : (t : M2) = Matrix.diagonal ![a, b]) (u : Kv) :
    (unipotentGL2 u)⁻¹ * t * unipotentGL2 u ∈
        localIntegralSet K v * ({dl} : Set (GL (Fin 2) Kv)) * localIntegralSet K v ↔
      ‖a * b‖ = ‖(ϖ : Kv)‖ ^ (m₁ + m₂) ∧ max (max ‖a‖ ‖b‖) ‖(a - b) * u‖ = ‖(ϖ : Kv)‖ ^ m₂ := by
  have hπ0 := uniformiser_ne_zero K v hϖ
  have hπ1 := norm_uniformiser_lt_one K v hϖ
  have hpos : 0 < ‖(ϖ : Kv)‖ ^ m₂ := zpow_pos (norm_uniformiser_pos K v hϖ) m₂
  rw [AutomorphicForm.mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm K v (ϖ : Kv) hπ0
    hπ1.le m₁ m₂ hm dl hdl, conj_diagonal_coe K v ht u, Matrix.det_fin_two_of, mul_zero, sub_zero]
  simp only [Fin.forall_fin_two, Fin.exists_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_zero]
  constructor
  · rintro ⟨hdet, ⟨⟨ha, hy⟩, -, hb⟩, hex⟩
    refine ⟨hdet, le_antisymm (max_le (max_le ha hb) hy) ?_⟩
    rcases hex with (h | h) | (h | h)
    · exact h.symm.le.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact h.symm.le.trans (le_max_right _ _)
    · exact absurd h hpos.ne
    · exact h.symm.le.trans ((le_max_right _ _).trans (le_max_left _ _))
  · rintro ⟨hdet, hmax⟩
    refine ⟨hdet, ⟨⟨?_, ?_⟩, hpos.le, ?_⟩, ?_⟩
    · exact (le_max_left _ _).trans ((le_max_left _ _).trans hmax.le)
    · exact (le_max_right _ _).trans hmax.le
    · exact (le_max_right _ _).trans ((le_max_left _ _).trans hmax.le)
    · rcases max_choice (max ‖a‖ ‖b‖) ‖(a - b) * u‖ with h | h
      · rw [h] at hmax
        rcases max_choice ‖a‖ ‖b‖ with h' | h'
        · exact Or.inl (Or.inl (h' ▸ hmax))
        · exact Or.inr (Or.inr (h' ▸ hmax))
      · exact Or.inl (Or.inr (h ▸ hmax))

end Fibre

section Main

theorem main {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {m₁ m₂ : ℤ} (hm : m₂ ≤ m₁)
    {dl : GL (Fin 2) Kv} (hdl : (dl : M2) = Matrix.diagonal ![(ϖ : Kv) ^ m₁, (ϖ : Kv) ^ m₂])
    {a b : Kv} (hab : a ≠ b) {t : GL (Fin 2) Kv} (ht : (t : M2) = Matrix.diagonal ![a, b])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ‖(ϖ : Kv)‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ∧
    (∀ u : Kv,
      (unipotentGL2 u)⁻¹ * t * unipotentGL2 u ∈
          localIntegralSet K v * ({dl} : Set (GL (Fin 2) Kv)) * localIntegralSet K v ↔
        ‖a * b‖ = ‖(ϖ : Kv)‖ ^ (m₁ + m₂) ∧ max (max ‖a‖ ‖b‖) ‖(a - b) * u‖ = ‖(ϖ : Kv)‖ ^ m₂) ∧
    (∀ n : ℤ, ‖a - b‖ * ν.real {u : Kv | ‖(a - b) * u‖ ≤ ‖(ϖ : Kv)‖ ^ n} =
      ‖(ϖ : Kv)‖ ^ n * ν.real (v.adicCompletionIntegers K : Set Kv)) ∧
    (∀ n : ℤ, ‖a - b‖ * ν.real {u : Kv | ‖(a - b) * u‖ = ‖(ϖ : Kv)‖ ^ n} =
      ‖(ϖ : Kv)‖ ^ n * (1 - ‖(ϖ : Kv)‖) * ν.real (v.adicCompletionIntegers K : Set Kv)) ∧
    ‖a - b‖ * ν.real {u : Kv | (unipotentGL2 u)⁻¹ * t * unipotentGL2 u ∈
        localIntegralSet K v * ({dl} : Set (GL (Fin 2) Kv)) * localIntegralSet K v} ≤
      ‖(ϖ : Kv)‖ ^ m₂ * ν.real (v.adicCompletionIntegers K : Set Kv) := by
  have hc : a - b ≠ 0 := sub_ne_zero.2 hab
  have hπpos := norm_uniformiser_pos K v hϖ
  have hπ1 := norm_uniformiser_lt_one K v hϖ
  have hfib := conj_mem_doubleCoset_iff K v hϖ hm hdl ht
  refine ⟨norm_uniformiser K v hϖ, hfib, fun n => norm_mul_measureReal_setOf_norm_mul_le K v hϖ hc n ν,
    fun n => norm_mul_measureReal_setOf_norm_mul_eq K v hϖ hc n ν, ?_⟩

  have hO : 0 ≤ ν.real (v.adicCompletionIntegers K : Set Kv) := measureReal_nonneg
  set F : Set Kv := {u : Kv | (unipotentGL2 u)⁻¹ * t * unipotentGL2 u ∈
      localIntegralSet K v * ({dl} : Set (GL (Fin 2) Kv)) * localIntegralSet K v} with hF
  by_cases hdet : ‖a * b‖ = ‖(ϖ : Kv)‖ ^ (m₁ + m₂)
  · rcases lt_trichotomy (max ‖a‖ ‖b‖) (‖(ϖ : Kv)‖ ^ m₂) with hlt | heq | hgt
    ·
      have hFeq : F = {u : Kv | ‖(a - b) * u‖ = ‖(ϖ : Kv)‖ ^ m₂} := by
        ext u
        simp only [hF, Set.mem_setOf_eq, hfib u, hdet, true_and]
        constructor
        · intro h
          rcases max_choice (max ‖a‖ ‖b‖) ‖(a - b) * u‖ with h' | h'
          · rw [h'] at h; exact absurd h hlt.ne
          · rw [h'] at h; exact h
        · intro h
          rw [max_eq_right (h.symm ▸ hlt.le), h]
      rw [hFeq, norm_mul_measureReal_setOf_norm_mul_eq K v hϖ hc m₂ ν]
      refine mul_le_mul_of_nonneg_right ?_ hO
      exact mul_le_of_le_one_right (zpow_nonneg (norm_nonneg _) _) (by linarith [norm_nonneg (ϖ : Kv)])
    ·
      have hFeq : F = {u : Kv | ‖(a - b) * u‖ ≤ ‖(ϖ : Kv)‖ ^ m₂} := by
        ext u
        simp only [hF, Set.mem_setOf_eq, hfib u, hdet, true_and, heq]
        constructor
        · intro h; exact h ▸ le_max_right _ _
        · intro h; exact max_eq_left h
      rw [hFeq, norm_mul_measureReal_setOf_norm_mul_le K v hϖ hc m₂ ν]
    ·
      have hFeq : F = ∅ := by
        ext u
        simp only [hF, Set.mem_setOf_eq, hfib u, hdet, true_and, Set.mem_empty_iff_false, iff_false]
        intro h
        have : max ‖a‖ ‖b‖ ≤ ‖(ϖ : Kv)‖ ^ m₂ := h ▸ le_max_left _ _
        exact absurd this (not_le.2 hgt)
      rw [hFeq, measureReal_empty, mul_zero]
      exact mul_nonneg (zpow_nonneg (norm_nonneg _) _) hO
  ·
    have hFeq : F = ∅ := by
      ext u
      simp only [hF, Set.mem_setOf_eq, hfib u, Set.mem_empty_iff_false, iff_false, not_and]
      intro h; exact absurd h hdet
    rw [hFeq, measureReal_empty, mul_zero]
    exact mul_nonneg (zpow_nonneg (norm_nonneg _) _) hO

end Main

end Local

end KcSplitTorusOrbitalR4

end

open MeasureTheory NumberField IsDedekindDomain
open scoped Pointwise

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (m₁ m₂ : ℤ) (hm : m₂ ≤ m₁)
    (dl : GL (Fin 2) (v.adicCompletion K))
    (hdl : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖ : v.adicCompletion K) ^ m₁, (ϖ : v.adicCompletion K) ^ m₂])
    (a b : v.adicCompletion K) (hab : a ≠ b) (t : GL (Fin 2) (v.adicCompletion K))
    (ht : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![a, b])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ‖(ϖ : v.adicCompletion K)‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ∧
    (∀ u : v.adicCompletion K,
      (AutomorphicForm.unipotentGL2 u)⁻¹ * t * AutomorphicForm.unipotentGL2 u ∈
          AutomorphicForm.localIntegralSet K v * ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
            AutomorphicForm.localIntegralSet K v ↔
        ‖a * b‖ = ‖(ϖ : v.adicCompletion K)‖ ^ (m₁ + m₂) ∧
          max (max ‖a‖ ‖b‖) ‖(a - b) * u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ m₂) ∧
    (∀ n : ℤ, ‖a - b‖ * ν.real {u : v.adicCompletion K | ‖(a - b) * u‖ ≤ ‖(ϖ : v.adicCompletion K)‖ ^ n} =
      ‖(ϖ : v.adicCompletion K)‖ ^ n * ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∧
    (∀ n : ℤ, ‖a - b‖ * ν.real {u : v.adicCompletion K | ‖(a - b) * u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ n} =
      ‖(ϖ : v.adicCompletion K)‖ ^ n * (1 - ‖(ϖ : v.adicCompletion K)‖) *
        ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∧
    ‖a - b‖ * ν.real {u : v.adicCompletion K |
        (AutomorphicForm.unipotentGL2 u)⁻¹ * t * AutomorphicForm.unipotentGL2 u ∈
          AutomorphicForm.localIntegralSet K v * ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
            AutomorphicForm.localIntegralSet K v} ≤
      ‖(ϖ : v.adicCompletion K)‖ ^ m₂ * ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  KcSplitTorusOrbitalR4.main K v hϖ hm hdl hab ht ν

end S_AutomorphicForm_unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le
end P2MW
export P2MW.S_AutomorphicForm_unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le (solution)
