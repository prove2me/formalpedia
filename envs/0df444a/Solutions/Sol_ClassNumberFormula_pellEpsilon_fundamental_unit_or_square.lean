-- Prove2me | solution 1 for ClassNumberFormula.pellEpsilon_fundamental_unit_or_square
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:17:39.620856+00:00
-- url     : https://prove2.me/submissions/6b9ddd44-4076-455f-b785-feb631165906

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker
import Definitions.Def_ClassNumberFormula_FormClassNumber

open NumberField

namespace CNPE
open Polynomial

variable {K : Type*} [Field K] [NumberField K]

section
variable (d : ℤ) (hns : ¬ IsSquare d) (hK : Module.finrank ℚ K = 2) (α : K) (hα : α ^ 2 = (d : K))
include hns hα

lemma not_rat (q : ℚ) : algebraMap ℚ K q ≠ α := by
  intro hq
  have : algebraMap ℚ K (q ^ 2) = algebraMap ℚ K (d : ℚ) := by
    rw [map_pow, hq, hα, map_intCast]
  have h2 := (algebraMap ℚ K).injective this
  exact hns (Rat.isSquare_intCast_iff.mp ⟨q, by rw [← h2]; ring⟩)

lemma linInd : LinearIndependent ℚ ![(1 : K), α] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht; simp at hst; exact ⟨hst, rfl⟩
  · exfalso
    apply not_rat d hns α hα (-s / t)
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have htK : algebraMap ℚ K t ≠ 0 := by simpa using ht
    rw [map_div₀, map_neg]
    field_simp
    linear_combination -hst

include hK
noncomputable def bas : Module.Basis (Fin 2) ℚ K :=
  basisOfLinearIndependentOfCardEqFinrank (linInd d hns α hα) (by simp [hK])

lemma bas0 : bas d hns hK α hα 0 = 1 := by simp [bas]
lemma bas1 : bas d hns hK α hα 1 = α := by simp [bas]

lemma coords (x : K) : ∃ r s : ℚ, x = algebraMap ℚ K r + algebraMap ℚ K s * α := by
  refine ⟨(bas d hns hK α hα).repr x 0, (bas d hns hK α hα).repr x 1, ?_⟩
  conv_lhs => rw [← (bas d hns hK α hα).sum_repr x]
  rw [Fin.sum_univ_two, bas0, bas1, Algebra.smul_def, Algebra.smul_def, mul_one]

lemma repr_comb (r s : ℚ) :
    (bas d hns hK α hα).repr (algebraMap ℚ K r + algebraMap ℚ K s * α) 0 = r ∧
    (bas d hns hK α hα).repr (algebraMap ℚ K r + algebraMap ℚ K s * α) 1 = s := by
  have : algebraMap ℚ K r + algebraMap ℚ K s * α = r • bas d hns hK α hα 0 + s • bas d hns hK α hα 1 := by
    rw [bas0, bas1, Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [this, map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  simp

lemma norm_eq (r s : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ K r + algebraMap ℚ K s * α) = r ^ 2 - d * s ^ 2 := by
  classical
  rw [Algebra.norm_eq_matrix_det (bas d hns hK α hα), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, bas0, bas1, mul_one]
  have e2 : (algebraMap ℚ K r + algebraMap ℚ K s * α) * α =
      algebraMap ℚ K (d * s) + algebraMap ℚ K r * α := by
    rw [map_mul, map_intCast]; linear_combination algebraMap ℚ K s * hα
  rw [e2, (repr_comb d hns hK α hα r s).1, (repr_comb d hns hK α hα r s).2,
    (repr_comb d hns hK α hα _ r).1, (repr_comb d hns hK α hα _ r).2]
  ring

lemma trace_eq (r s : ℚ) :
    Algebra.trace ℚ K (algebraMap ℚ K r + algebraMap ℚ K s * α) = 2 * r := by
  classical
  rw [Algebra.trace_eq_matrix_trace (bas d hns hK α hα), Matrix.trace_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, bas0, bas1, mul_one]
  have e2 : (algebraMap ℚ K r + algebraMap ℚ K s * α) * α =
      algebraMap ℚ K (d * s) + algebraMap ℚ K r * α := by
    rw [map_mul, map_intCast]; linear_combination algebraMap ℚ K s * hα
  rw [e2, (repr_comb d hns hK α hα r s).1, (repr_comb d hns hK α hα _ r).2]
  ring

lemma adjoin_top : Algebra.adjoin ℚ {α} = ⊤ := by
  have htop : IntermediateField.adjoin ℚ {α} = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.finrank_top', hK]
    have hd : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) ∣ 2 := by
      rw [← hK, ← IntermediateField.finrank_top' (F := ℚ) (E := K)]
      exact IntermediateField.finrank_dvd_of_le_right le_top
    have hne : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) ≠ 1 := by
      rw [Ne, IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff,
        IntermediateField.mem_bot]
      rintro ⟨q, hq⟩
      exact not_rat d hns α hα q hq
    have hpos : 0 < Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) := Module.finrank_pos
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) <;> simp_all
  exact (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α)).mp htop

/-- an algebra hom determined by the image of α -/
lemma exists_hom {L : Type*} [Field L] [Algebra ℚ L] (β : L) (hβ : β ^ 2 = (d : L)) :
    ∃ σ : K →ₐ[ℚ] L, σ α = β := by
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  let pb := PowerBasis.ofAdjoinEqTop hint (adjoin_top d hns hK α hα)
  have hgen : pb.gen = α := PowerBasis.ofAdjoinEqTop_gen _ _
  have hmin : minpoly ℚ α ∣ X ^ 2 - C (d : ℚ) := by
    apply minpoly.dvd
    simp [hα]
  refine ⟨pb.lift β ?_, ?_⟩
  · rw [hgen]
    obtain ⟨q, hq⟩ := hmin
    -- aeval β (X^2 - d) = 0, so the minimal polynomial also kills β unless... use degree argument
    have hdeg : (minpoly ℚ α).natDegree = 2 := by
      rw [← IntermediateField.adjoin.finrank hint]
      have h := IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic α) |>.mpr (adjoin_top d hns hK α hα)
      rw [h, IntermediateField.finrank_top', hK]
    have hmon : (X ^ 2 - C (d : ℚ)).Monic := by
      apply Polynomial.monic_X_pow_sub_C; norm_num
    have heq : minpoly ℚ α = X ^ 2 - C (d : ℚ) := by
      refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon ⟨q, hq⟩ ?_).symm
      rw [hdeg, Polynomial.natDegree_X_pow_sub_C]
    rw [heq]; simp [hβ]
  · conv_lhs => arg 2; rw [← hgen]
    exact PowerBasis.lift_gen _ _ _

end

end CNPE


namespace CNPell
open ClassNumberFormula

lemma sq_squarefree {k : ℤ} (h : Squarefree (k * k)) : IsUnit k := h k dvd_rfl

lemma not_isSquare (d : ℤ) (hd : IsFundamentalDiscriminant d) (hpos : 0 < d) : ¬ IsSquare d := by
  rintro ⟨k, rfl⟩
  obtain ⟨h1, h2 | ⟨m, hm, hm4, hmsq⟩⟩ := hd
  · have hu := sq_squarefree h2.2
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp at h1
  · -- 4m = k*k ⇒ k even ⇒ m = (k/2)^2
    have hk2 : 2 ∣ k := by
      have : (2 : ℤ) ∣ k * k := ⟨2 * m, by rw [hm]; ring⟩
      exact (Int.prime_two.dvd_mul.mp this).elim id id
    obtain ⟨j, rfl⟩ := hk2
    have hmj : m = j * j := by linarith
    rw [hmj] at hmsq hm4
    have hu := sq_squarefree hmsq
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> norm_num at hm4

theorem main (d : ℤ) (hd : IsFundamentalDiscriminant d) (hpos : 0 < d) :
    ∃ t u : ℕ, 0 < t ∧ 0 < u ∧ (t : ℤ) ^ 2 - d * (u : ℤ) ^ 2 = 4 := by
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare hpos (not_isSquare d hd hpos)
  have hx : x ≠ 0 := by
    rintro rfl
    have : 0 ≤ d * y ^ 2 := by positivity
    linarith
  refine ⟨2 * x.natAbs, 2 * y.natAbs, by positivity, by positivity, ?_⟩
  push_cast
  have h1 : |x| ^ 2 = x ^ 2 := sq_abs x
  have h2 : |y| ^ 2 = y ^ 2 := sq_abs y
  nlinarith [h1, h2]

end CNPell


namespace CNPE2
open ClassNumberFormula

lemma int_of_sqfree (n : ℤ) (hn : Squarefree n) (Y : ℚ) (k : ℤ) (h : (n : ℚ) * Y ^ 2 = k) :
    ∃ y : ℤ, Y = y := by
  refine ⟨Y.num, ?_⟩
  have hden : (Y.den : ℤ) = 1 := by
    have hY : Y = Y.num / Y.den := (Rat.num_div_den Y).symm
    have hd0 : (Y.den : ℚ) ≠ 0 := by positivity
    have h2 : (n * Y.num ^ 2 : ℤ) = k * (Y.den : ℤ) ^ 2 := by
      have : (n : ℚ) * Y.num ^ 2 = k * Y.den ^ 2 := by
        rw [← Rat.mul_den_eq_num, ← h]; ring
      exact_mod_cast this
    have hcop : IsCoprime ((Y.den : ℤ) ^ 2) (Y.num ^ 2) := by
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := Y.reduced
      rw [Int.gcd_comm]
      simpa [Int.gcd, Nat.coprime_comm] using this
    have hdvd : (Y.den : ℤ) ^ 2 ∣ n * Y.num ^ 2 := ⟨k, by rw [h2]; ring⟩
    have hdvd2 : (Y.den : ℤ) ^ 2 ∣ n := hcop.dvd_of_dvd_mul_right hdvd
    have hu := hn (Y.den : ℤ) (by rw [← sq]; exact hdvd2)
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact h1
    · have : (0 : ℤ) < Y.den := by exact_mod_cast Y.den_pos
      omega
  have : Y.den = 1 := by exact_mod_cast hden
  exact (Rat.coe_int_num_of_den_eq_one this).symm

lemma intY (d : ℤ) (hd : IsFundamentalDiscriminant d) (X : ℤ) (Y : ℚ)
    (h : (X : ℚ) ^ 2 - d * Y ^ 2 = 4) : ∃ y : ℤ, Y = y := by
  obtain ⟨_, ⟨_, hsq⟩ | ⟨m, rfl, hm4, hmsq⟩⟩ := hd
  · exact int_of_sqfree d hsq Y (X ^ 2 - 4) (by push_cast; linarith)
  · obtain ⟨z, hz⟩ := int_of_sqfree m hmsq (2 * Y) (X ^ 2 - 4) (by push_cast at h ⊢; linarith)
    have hz2 : X ^ 2 - m * z ^ 2 = 4 := by
      have : (X : ℚ) ^ 2 - m * (z : ℚ) ^ 2 = 4 := by rw [← hz]; push_cast at h; linarith
      exact_mod_cast this
    obtain ⟨w, hw⟩ | ⟨w, hw⟩ := Int.even_or_odd z
    · refine ⟨w, ?_⟩
      have : (2 : ℚ) * Y = 2 * w := by rw [hz, hw]; push_cast; ring
      linarith
    · exfalso
      subst hw
      obtain ⟨v, hv⟩ | ⟨v, hv⟩ := Int.even_or_odd X
      · subst hv
        have : m * (2 * w + 1) ^ 2 = 4 * (v ^ 2 - 1) := by linarith
        have h4 : (4 : ℤ) ∣ m * (2 * w + 1) ^ 2 := ⟨v ^ 2 - 1, this⟩
        have : m * (2 * w + 1) ^ 2 = m + 4 * (m * (w ^ 2 + w)) := by ring
        rw [this] at h4
        omega
      · subst hv
        have : m * (2 * w + 1) ^ 2 = 4 * (v ^ 2 + v) + 1 - 4 := by linarith
        have : m + 4 * (m * (w ^ 2 + w)) = 4 * (v ^ 2 + v) - 3 := by linarith
        omega

end CNPE2


open NumberField NumberField.Units ClassNumberFormula

namespace CNPE3

lemma pell_facts (d : ℤ) (hd : IsFundamentalDiscriminant d) (hpos : 0 < d) :
    0 < pellU d ∧ 0 < pellT d ∧ (pellT d : ℤ) ^ 2 - d * (pellU d : ℤ) ^ 2 = 4 ∧
      ∀ t u : ℕ, 0 < t → 0 < u → (t : ℤ) ^ 2 - d * (u : ℤ) ^ 2 = 4 → pellU d ≤ u := by
  obtain ⟨t0, u0, ht0, hu0, h0⟩ := CNPell.main d hd hpos
  have hS : u0 ∈ {u : ℕ | 0 < u ∧ ∃ t : ℕ, 0 < t ∧ (t : ℤ) ^ 2 - d * (u : ℤ) ^ 2 = 4} :=
    ⟨hu0, t0, ht0, h0⟩
  have hU := Nat.sInf_mem ⟨u0, hS⟩
  obtain ⟨hUpos, t1, ht1, h1⟩ := hU
  have hT := Nat.sInf_mem (s := {t : ℕ | 0 < t ∧ (t : ℤ) ^ 2 - d * (pellU d : ℤ) ^ 2 = 4})
    ⟨t1, ht1, h1⟩
  refine ⟨hUpos, hT.1, hT.2, fun t u ht hu h => Nat.sInf_le ⟨hu, t, ht, h⟩⟩

variable {K : Type*} [Field K] [NumberField K]

lemma rat_int_of_integral (x : 𝓞 K) : ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ K (x : K) := by
  have h : IsIntegral ℤ (Algebra.trace ℚ K (x : K)) := Algebra.isIntegral_trace x.2
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨y, by simpa using hy⟩

section
variable (d : ℤ) (hd : IsFundamentalDiscriminant d) (hpos : 0 < d)
  (hK : Module.finrank ℚ K = 2) (α : K) (hα : α ^ 2 = (d : K))
  (σ : K →ₐ[ℚ] ℝ) (hσ : σ α = Real.sqrt d)
include hd hpos hK hα hσ

lemma sv_lower (w : 𝓞 K) (hN : Algebra.norm ℚ (w : K) = 1) (hw : 1 < σ (w : K)) :
    ((pellT d : ℝ) + pellU d * Real.sqrt d) / 2 ≤ σ (w : K) := by
  have hns := CNPell.not_isSquare d hd hpos
  obtain ⟨r, s, hrs⟩ := CNPE.coords d hns hK α hα (w : K)
  rw [hrs, CNPE.norm_eq d hns hK α hα] at hN
  obtain ⟨X, hX⟩ := rat_int_of_integral w
  rw [hrs, CNPE.trace_eq d hns hK α hα] at hX
  have hσw : σ (w : K) = (r : ℝ) + (s : ℝ) * Real.sqrt d := by
    rw [hrs, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσ]; rfl
  obtain ⟨y, hy⟩ := CNPE2.intY d hd X (2 * s) (by rw [hX]; linear_combination 4 * hN)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hpos
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hdR.le
  have hN' : (r : ℝ) ^ 2 - d * (s : ℝ) ^ 2 = 1 := by exact_mod_cast hN
  rw [hσw] at hw ⊢
  have hprod : ((r : ℝ) - s * Real.sqrt d) * ((r : ℝ) + s * Real.sqrt d) = 1 := by
    linear_combination hN' - (s : ℝ) ^ 2 * hsq
  have hpos2 : 0 < (r : ℝ) - s * Real.sqrt d := by
    by_contra hc; push Not at hc; nlinarith
  have hlt : (r : ℝ) - s * Real.sqrt d < 1 := by
    by_contra hc; push Not at hc; nlinarith
  have hr : 0 < (r : ℝ) := by linarith
  have hsd : 0 < (s : ℝ) * Real.sqrt d := by linarith
  have hX' : (X : ℝ) = 2 * r := by exact_mod_cast hX
  have hy' : (y : ℝ) = 2 * s := by exact_mod_cast hy.symm
  have hXpos : 0 < X := by
    have : (0 : ℝ) < X := by rw [hX']; linarith
    exact_mod_cast this
  have hsqd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hypos : 0 < y := by
    have : (0 : ℝ) < y := by
      rw [hy']; have := (pos_iff_pos_of_mul_pos hsd).mpr hsqd; linarith
    exact_mod_cast this
  have hXy : X ^ 2 - d * y ^ 2 = 4 := by
    have : (X : ℝ) ^ 2 - d * (y : ℝ) ^ 2 = 4 := by rw [hX', hy']; linear_combination 4 * hN'
    exact_mod_cast this
  obtain ⟨hU, hT, hTU, hmin⟩ := pell_facts d hd hpos
  have hle := hmin X.toNat y.toNat (by omega) (by omega)
    (by rw [Int.toNat_of_nonneg hXpos.le, Int.toNat_of_nonneg hypos.le]; exact hXy)
  have hUy : (pellU d : ℤ) ≤ y := by
    have := Int.toNat_of_nonneg hypos.le
    omega
  have hTX : (pellT d : ℤ) ≤ X := by
    have h1 : (pellT d : ℤ) ^ 2 ≤ X ^ 2 := by
      have : d * (pellU d : ℤ) ^ 2 ≤ d * y ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hpos.le
        exact pow_le_pow_left₀ (by positivity) hUy 2
      linarith
    have h0 : (0 : ℤ) ≤ pellT d := by positivity
    nlinarith
  have hUyR : (pellU d : ℝ) ≤ y := by exact_mod_cast hUy
  have hTXR : (pellT d : ℝ) ≤ X := by exact_mod_cast hTX
  have : (pellU d : ℝ) * Real.sqrt d ≤ y * Real.sqrt d := mul_le_mul_of_nonneg_right hUyR hsqd.le
  rw [hX'] at hTXR; rw [hy'] at this
  linarith

end

lemma eps_integral (d : ℤ) (α : K) (hα : α ^ 2 = (d : K)) (T U : ℕ) (hTU : (T : ℤ) ^ 2 - d * (U : ℤ) ^ 2 = 4) :
    IsIntegral ℤ (((T : K) + (U : K) * α) / 2) := by
  refine ⟨Polynomial.X ^ 2 + (Polynomial.C (-(T : ℤ)) * Polynomial.X + Polynomial.C 1), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  · simp
    have h4 : ((T : K)) ^ 2 - (d : K) * (U : K) ^ 2 = 4 := by exact_mod_cast hTU
    linear_combination (1 / 4 : K) * (U : K) ^ 2 * hα - (1 / 4 : K) * h4

lemma torsion_pm (σ : K →ₐ[ℚ] ℝ) (ζ : (𝓞 K)ˣ) (hζ : ζ ∈ torsion K) : ζ = 1 ∨ ζ = -1 := by
  rw [torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one] at hζ
  obtain ⟨n, hn, h⟩ := hζ
  have h1 : (σ (ζ : K)) ^ n = 1 := by
    rw [← map_pow, ← coe_pow, h, coe_one, map_one]
  have h2 : |σ (ζ : K)| = 1 := by
    rw [← pow_left_inj₀ (abs_nonneg _) zero_le_one hn.ne', pow_abs, h1, abs_one, one_pow]
  have hinj : Function.Injective σ := σ.toRingHom.injective
  rcases abs_eq (zero_le_one) |>.mp h2 with h3 | h3
  · left; apply coe_injective; apply hinj; rw [h3]; simp
  · right; apply coe_injective; apply hinj; rw [h3]; simp

lemma gen_inv (f : (𝓞 K)ˣ) (hf : ∀ v : (𝓞 K)ˣ, ∃ n : ℤ, v = f ^ n ∨ v = -f ^ n) :
    ∀ v : (𝓞 K)ˣ, ∃ n : ℤ, v = f⁻¹ ^ n ∨ v = -f⁻¹ ^ n := by
  intro v
  obtain ⟨n, h⟩ := hf v
  exact ⟨-n, by simpa [inv_zpow', neg_neg] using h⟩

lemma gen_neg (f : (𝓞 K)ˣ) (hf : ∀ v : (𝓞 K)ˣ, ∃ n : ℤ, v = f ^ n ∨ v = -f ^ n) :
    ∀ v : (𝓞 K)ˣ, ∃ n : ℤ, v = (-f) ^ n ∨ v = -(-f) ^ n := by
  intro v
  obtain ⟨n, h⟩ := hf v
  refine ⟨n, ?_⟩
  rcases Int.even_or_odd n with he | ho
  · rw [he.neg_zpow]; exact h
  · rw [ho.neg_zpow, neg_neg]; exact h.symm

lemma sig_zpow (σ : K →ₐ[ℚ] ℝ) (v : (𝓞 K)ˣ) (n : ℤ) : σ ((v ^ n : (𝓞 K)ˣ) : K) = σ (v : K) ^ n := by
  rw [coe_zpow, map_zpow₀]

lemma sig_neg (σ : K →ₐ[ℚ] ℝ) (v : (𝓞 K)ˣ) : σ ((-v : (𝓞 K)ˣ) : K) = -σ (v : K) := by
  have : ((-v : (𝓞 K)ˣ) : K) = -(v : K) := by
    rw [show -v = (-1) * v by simp, coe_mul, coe_neg_one]; ring
  rw [this, map_neg]

lemma sig_ne (σ : K →ₐ[ℚ] ℝ) (v : (𝓞 K)ˣ) : σ (v : K) ≠ 0 := by
  exact (map_ne_zero σ).mpr (coe_ne_zero v)

theorem main (d : ℤ) (hd : IsFundamentalDiscriminant d)
    (hpos : 0 < d) (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (α : K) (hα : α ^ 2 = (d : K)) :
    ∃ η : (𝓞 K)ˣ, (∀ v : (𝓞 K)ˣ, ∃ n : ℤ, v = η ^ n ∨ v = -η ^ n) ∧
      (((η : 𝓞 K) : K) = ((pellT d : K) + (pellU d : K) * α) / 2 ∨
        ((η : 𝓞 K) : K) ^ 2 = ((pellT d : K) + (pellU d : K) * α) / 2) := by
  classical
  have hns := CNPell.not_isSquare d hd hpos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hpos
  obtain ⟨σ, hσ⟩ := CNPE.exists_hom d hns hK α hα (L := ℝ) (Real.sqrt d)
    (by rw [Real.sq_sqrt hdR.le])
  obtain ⟨hU, hT, hTU, -⟩ := pell_facts d hd hpos
  have hεint := eps_integral d α hα (pellT d) (pellU d) hTU
  let εO : 𝓞 K := ⟨_, hεint⟩
  have hεO : ((εO : 𝓞 K) : K) = ((pellT d : K) + (pellU d : K) * α) / 2 := rfl
  have hinvO : εO * ((pellT d : 𝓞 K) - εO) = 1 := by
    apply RingOfIntegers.coe_injective
    have h4 : ((pellT d : K)) ^ 2 - (d : K) * (pellU d : K) ^ 2 = 4 := by exact_mod_cast hTU
    simp only [map_mul, map_sub, map_natCast, map_one, hεO]
    linear_combination (1 / 4 : K) * h4 - (1 / 4 : K) * (pellU d : K) ^ 2 * hα
  let εu : (𝓞 K)ˣ := Units.mkOfMulEqOne εO _ hinvO
  have hεu : ((εu : 𝓞 K) : K) = ((pellT d : K) + (pellU d : K) * α) / 2 := rfl
  have hsqd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hsε : σ ((εu : 𝓞 K) : K) = ((pellT d : ℝ) + pellU d * Real.sqrt d) / 2 := by
    rw [hεu, map_div₀, map_add, map_mul, hσ, map_ofNat]; simp
  have hε1 : 1 < σ ((εu : 𝓞 K) : K) := by
    rw [hsε]
    have hT3 : (3 : ℤ) ≤ pellT d := by
      have : (1 : ℤ) ≤ pellU d := by exact_mod_cast hU
      have : (1 : ℤ) ≤ d := hpos
      have h5 : (5 : ℤ) ≤ (pellT d : ℤ) ^ 2 := by nlinarith
      nlinarith
    have : (3 : ℝ) ≤ pellT d := by exact_mod_cast hT3
    have : 0 ≤ (pellU d : ℝ) * Real.sqrt d := by positivity
    linarith
  -- rank
  have hr1 : rank K ≤ 1 := by
    have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    have h2 := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
    unfold rank; omega
  have hr0 : rank K ≠ 0 := by
    intro h
    obtain ⟨⟨ζ, e⟩, hx, -⟩ := exist_unique_eq_mul_prod K εu
    have : IsEmpty (Fin (rank K)) := by rw [h]; infer_instance
    rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hx
    rcases torsion_pm σ ζ ζ.2 with h' | h' <;> rw [h'] at hx <;> rw [hx] at hε1 <;> simp at hε1 <;> linarith
  let i0 : Fin (rank K) := ⟨0, by omega⟩
  let f := fundSystem K i0
  have hf : ∀ v : (𝓞 K)ˣ, ∃ n : ℤ, v = f ^ n ∨ v = -f ^ n := by
    intro v
    obtain ⟨⟨ζ, e⟩, hx, -⟩ := exist_unique_eq_mul_prod K v
    rw [Finset.prod_eq_single i0 (fun b _ hb => (hb (Fin.ext (by omega))).elim) (by simp)] at hx
    refine ⟨e i0, ?_⟩
    rcases torsion_pm σ ζ ζ.2 with h' | h' <;> simp only at hx <;> rw [h'] at hx
    · left; simpa using hx
    · right; simpa using hx
  have hsv : ∀ η : (𝓞 K)ˣ, (∀ v : (𝓞 K)ˣ, ∃ n : ℤ, v = η ^ n ∨ v = -η ^ n) →
      ∀ v : (𝓞 K)ˣ, ∃ n : ℤ, σ (v : K) = σ (η : K) ^ n ∨ σ (v : K) = -σ (η : K) ^ n := by
    intro η hη v
    obtain ⟨n, h | h⟩ := hη v
    · exact ⟨n, Or.inl (by rw [h, sig_zpow])⟩
    · exact ⟨n, Or.inr (by rw [h, sig_neg, sig_zpow])⟩
  -- normalize
  have hs1 : |σ (f : K)| ≠ 1 := by
    intro h
    obtain ⟨n, h' | h'⟩ := hsv f hf εu
    · have : |σ ((εu : 𝓞 K) : K)| = 1 := by rw [h', abs_zpow, h, one_zpow]
      rw [abs_of_pos (by linarith)] at this; linarith
    · have : |σ ((εu : 𝓞 K) : K)| = 1 := by rw [h', abs_neg, abs_zpow, h, one_zpow]
      rw [abs_of_pos (by linarith)] at this; linarith
  have hs0 := sig_ne σ f
  obtain ⟨η, hη, hη1⟩ : ∃ η : (𝓞 K)ˣ, (∀ v : (𝓞 K)ˣ, ∃ n : ℤ, v = η ^ n ∨ v = -η ^ n) ∧
      1 < σ (η : K) := by
    have hfi : σ ((f⁻¹ : (𝓞 K)ˣ) : K) = (σ (f : K))⁻¹ := by
      rw [← zpow_neg_one, sig_zpow, zpow_neg_one]
    rcases lt_or_gt_of_ne hs0 with hneg | hpos'
    · rcases lt_or_gt_of_ne (show σ (f : K) ≠ -1 from fun h => hs1 (by rw [h]; simp)) with h | h
      · exact ⟨-f, gen_neg f hf, by rw [sig_neg]; linarith⟩
      · refine ⟨-f⁻¹, gen_neg _ (gen_inv f hf), ?_⟩
        rw [sig_neg, hfi]
        have hm : σ (f : K) * (σ (f : K))⁻¹ = 1 := mul_inv_cancel₀ hs0
        have : (σ (f : K))⁻¹ < -1 := by
          by_contra hc; push Not at hc; nlinarith
        linarith
    · rcases lt_or_gt_of_ne (show σ (f : K) ≠ 1 from fun h => hs1 (by rw [h]; simp)) with h | h
      · refine ⟨f⁻¹, gen_inv f hf, ?_⟩
        rw [hfi]; exact one_lt_inv₀ hpos' |>.mpr h
      · exact ⟨f, hf, h⟩
  refine ⟨η, hη, ?_⟩
  obtain ⟨k, hk | hk⟩ := hη εu
  · have hσk : σ ((εu : 𝓞 K) : K) = σ (η : K) ^ k := by rw [hk, sig_zpow]
    have hk1 : 1 ≤ k := by
      by_contra hc; push Not at hc
      have : σ (η : K) ^ k ≤ 1 := zpow_le_one_of_nonpos₀ hη1.le (by omega)
      linarith
    have hk2 : k ≤ 2 := by
      by_contra hc; push Not at hc
      -- lower bound applied to η²
      have hN : Algebra.norm ℚ (((η ^ 2 : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by
        have h1 := NumberField.Units.norm K η
        rw [show (((η ^ 2 : (𝓞 K)ˣ) : 𝓞 K) : K) = ((η : 𝓞 K) : K) ^ 2 by push_cast; rfl, map_pow]
        rcases abs_eq zero_le_one |>.mp h1 with h | h <;> rw [h] <;> norm_num
      have hσ2 : σ (((η ^ 2 : (𝓞 K)ˣ) : 𝓞 K) : K) = σ (η : K) ^ 2 := by
        rw [show (((η ^ 2 : (𝓞 K)ˣ) : 𝓞 K) : K) = ((η : 𝓞 K) : K) ^ 2 by push_cast; rfl, map_pow]
      have hlow := sv_lower d hd hpos hK α hα σ hσ _ hN (by rw [hσ2]; nlinarith)
      rw [hσ2, ← hsε, hσk] at hlow
      have : σ (η : K) ^ (2 : ℤ) < σ (η : K) ^ k := zpow_lt_zpow_right₀ hη1 hc
      rw [zpow_two] at this; rw [sq] at hlow
      linarith
    interval_cases k
    · left; rw [← hεu, hk, zpow_one]
    · right; rw [← hεu, hk]; simp [sq]
  · exfalso
    have : σ ((εu : 𝓞 K) : K) = -σ (η : K) ^ k := by rw [hk, sig_neg, sig_zpow]
    have : 0 < σ (η : K) ^ k := zpow_pos (by linarith) k
    linarith

end CNPE3

open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real ClassNumberFormula

theorem solution (d : ℤ) (hd : IsFundamentalDiscriminant d)
    (hpos : 0 < d) (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (α : K) (hα : α ^ 2 = (d : K)) :
    ∃ η : (𝓞 K)ˣ, (∀ v : (𝓞 K)ˣ, ∃ n : ℤ, v = η ^ n ∨ v = -η ^ n) ∧
      (((η : 𝓞 K) : K) = ((pellT d : K) + (pellU d : K) * α) / 2 ∨
        ((η : 𝓞 K) : K) ^ 2 = ((pellT d : K) + (pellU d : K) * α) / 2) :=
  CNPE3.main d hd hpos K hK α hα
