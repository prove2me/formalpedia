-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.kappaAssembly_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:16.466373+00:00
-- url     : https://prove2.me/submissions/df106806-c230-4b5f-b97e-24ba4591aff7

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sq_sum_fin_b
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_dimN_eq_b
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_vsph_pos_b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hV : VRatio) : KappaAssembly := by
  obtain ⟨Cv, hCv, hV⟩ := hV
  intro C hC
  have hC7 : 1 ≤ C ^ 7 := one_le_pow₀ hC
  refine ⟨C ^ 7 * Cv, by nlinarith, ?_⟩
  intro a p q n0 f j v res cIw volN volR volGL hj ha hJq hqp hn hf hv hres hN0 hN hGL hR0 hR hI0 hI
  have hVr := hV p q a j hJq hqp
  have hsq := sq_sum_fin_b j
  have hdim := dimN_eq_b j n0
  have haJ : a ≤ ∑ x, j x := by
    calc a = ∑ _x : Fin a, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun x _ => hj x
  set J := ∑ x, j x with hJ
  set dN := dimN j n0 with hdN
  set Q := ∑ x, j x ^ 2 with hQ
  set P := ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y with hP
  set JJ : ℝ := (J : ℝ) ^ ((J : ℝ) ^ 2 / 2) with hJJ
  set R : ℝ := Vsph p * Vsph q / (Vsph (p - J) * Vsph (q - J) * ∏ x, Vsph (j x)) with hRdef
  have hC0 : 0 < C := by linarith
  have hCv0 : 0 < Cv := by linarith
  have hv0 : 0 < v := by linarith
  have hJJ0 : 0 ≤ JJ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hR0' : 0 ≤ R := by
    have := vsph_pos_b p; have := vsph_pos_b q; have := vsph_pos_b (p - J); have := vsph_pos_b (q - J)
    have : 0 < ∏ x, Vsph (j x) := Finset.prod_pos fun x _ => vsph_pos_b _
    positivity
  have hJ1 : 1 ≤ J := le_trans ha haJ

  have hexp : dN * f + dN * f + Q * f + a * f + (p + q) * f ≤ 7 * (J * (p + q) * f) := by
    have hn1 : J ≤ p + q := by omega
    have h1 : dN ≤ 2 * (J * (p + q)) := by
      rw [hdim, hn]; nlinarith
    have h2 : Q ≤ J * (p + q) := by
      calc Q ≤ J ^ 2 := by omega
        _ = J * J := sq J
        _ ≤ _ := Nat.mul_le_mul_left _ hn1
    have h3 : p + q ≤ J * (p + q) := Nat.le_mul_of_pos_left _ hJ1
    have h4 : a ≤ J * (p + q) := by
      calc a ≤ J := haJ
        _ ≤ p + q := hn1
        _ ≤ _ := h3
    calc dN * f + dN * f + Q * f + a * f + (p + q) * f = (dN + dN + Q + a + (p + q)) * f := by ring
      _ ≤ (7 * (J * (p + q))) * f := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring

  have hid : ((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2 = 2 * (Q : ℝ) + 2 * (dN : ℝ) := by
    have : (p + q) ^ 2 = n0 ^ 2 + 2 * Q + 2 * dN := by
      rw [hdim, hn]; nlinarith
    have h' : ((p + q : ℕ) : ℝ) ^ 2 = (n0 : ℝ) ^ 2 + 2 * Q + 2 * dN := by exact_mod_cast this
    linarith
  set W : ℝ := (Cv / (p : ℝ)) ^ (J * (p - J)) * JJ with hW
  set W' : ℝ := (C ^ 7 * Cv / (p : ℝ)) ^ (J * (p - J)) * JJ with hW'
  have hW0 : 0 ≤ W := by positivity
  have hWW : W ≤ W' := by
    rw [hW, hW']
    gcongr
    nlinarith
  have sA : cIw ≤ C ^ (dN * f) * (Cv ^ (J * (p + q) * f) * W ^ f) := by
    refine hI.trans ?_
    calc (C ^ dN * R) ^ f ≤ (C ^ dN * (Cv ^ (J * (p + q)) * W)) ^ f := by
          gcongr
          rw [hW, ← mul_assoc]; exact hVr
      _ = _ := by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  have sB : volN ≤ C ^ (dN * f) * v ^ ((f : ℝ) * dN / 2) := by
    refine hN.trans ?_
    rw [Real.mul_rpow hC0.le hv0.le]
    gcongr
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hC
    push_cast
    have : (0:ℝ) ≤ (f:ℝ) * dN := by positivity
    linarith
  have sC : ∏ x, volGL x ≤ C ^ (Q * f) * v ^ ((Q : ℝ) * f) * res ^ a * C ^ (a * f) := by
    calc ∏ x, volGL x ≤ ∏ x, ((C * v) ^ (j x ^ 2 * f) * res * C ^ f) :=
          Finset.prod_le_prod (fun x _ => (hGL x).1) (fun x _ => (hGL x).2)
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
            Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.sum_mul,
            mul_pow, ← pow_mul, mul_comm f a]
          congr 3
          rw [← Real.rpow_natCast, Nat.cast_mul]
  have hG0 : 0 ≤ ∏ x, volGL x := Finset.prod_nonneg fun x _ => (hGL x).1
  have hvv : v ^ ((f : ℝ) * dN / 2) * v ^ ((Q : ℝ) * f)
      * v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * f / 2) = v ^ (-((f : ℝ) * dN / 2)) := by
    rw [← Real.rpow_add hv0, ← Real.rpow_add hv0, hid]
    congr 1; ring
  have hvp : 0 < v ^ (-((f : ℝ) * dN / 2)) := Real.rpow_pos_of_pos hv0 _
  have key : ∀ c1 k w v1 c3 v2 r c4 v3 c5 : ℝ, (c1 * (k * w)) * (c1 * v1) * (c3 * v2 * r * c4) * (v3 * c5)
      = (v1 * v2 * v3) * (c1 * c1 * c3 * c4 * c5 * k) * r * w := by intros; ring
  have key2 : ∀ x c c' k r w w' : ℝ, 0 ≤ x → 0 ≤ c → 0 ≤ k → 0 ≤ r → 0 ≤ w → c ≤ c' → w ≤ w' →
      x * (c * k) * r * w ≤ x * (c' * k) * r * w' := by
    intro x c c' k r w w' _ hc _ _ _ hcc _
    have : 0 ≤ c' := hc.trans hcc
    gcongr
  calc cIw * volN * (∏ x, volGL x) * volR
      ≤ (C ^ (dN * f) * (Cv ^ (J * (p + q) * f) * W ^ f)) * (C ^ (dN * f) * v ^ ((f : ℝ) * dN / 2))
        * (C ^ (Q * f) * v ^ ((Q : ℝ) * f) * res ^ a * C ^ (a * f))
        * (v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * f / 2) * C ^ ((p + q) * f)) := by
        gcongr
    _ = (v ^ ((f : ℝ) * dN / 2) * v ^ ((Q : ℝ) * f)
          * v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * f / 2))
        * (C ^ (dN * f + dN * f + Q * f + a * f + (p + q) * f) * Cv ^ (J * (p + q) * f))
        * res ^ a * W ^ f := by
        rw [pow_add, pow_add, pow_add, pow_add]
        exact key _ _ _ _ _ _ _ _ _ _
    _ ≤ v ^ (-((f : ℝ) * dN / 2)) * (C ^ (7 * (J * (p + q) * f)) * Cv ^ (J * (p + q) * f))
        * res ^ a * W' ^ f := by
        rw [hvv]
        exact key2 _ _ _ _ _ _ _ hvp.le (by positivity) (by positivity) (by positivity)
          (pow_nonneg hW0 f) (pow_le_pow_right₀ hC hexp) (pow_le_pow_left₀ hW0 hWW f)
    _ = _ := by
        rw [pow_mul C 7, ← mul_pow]
end Formalism.HermitianLatticeCounting.P
