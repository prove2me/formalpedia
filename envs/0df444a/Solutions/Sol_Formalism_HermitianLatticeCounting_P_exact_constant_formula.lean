-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.exact_constant_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:05.5981+00:00
-- url     : https://prove2.me/submissions/c751371d-f4e2-490e-9870-a34dab2b8b2a

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LocalIntegralStructure_constProduct
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LocalIntegralStructure_tcritForm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ConstExact := by
  intro j r T T' g v th dimpi Vd VV Tc hT hT' hg hv hth hVd hVV hTc hdef
  have hpi := Real.pi_pos
  have he := Real.exp_pos 1
  have hk : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hjf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  have hM1 : (2 * r + 2) * (2 * r + 1) / 2 = 2 * r ^ 2 + r + (2 * r + 1) := by
    have : (2 * r + 2) * (2 * r + 1) = 2 * (2 * r ^ 2 + r + (2 * r + 1)) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hM2 : (2 * r + 1) * (2 * r + 2) / 2 = 2 * r ^ 2 + r + (2 * r + 1) := by
    rw [mul_comm, hM1]
  set κ : ℝ := (Real.exp 1 / ((j + 1 : ℕ) : ℝ)) ^ (j + 1) * (j.factorial : ℝ) with hκ
  set n0 : ℝ := (Real.exp 1 * Real.pi / (g ^ (2 * r + 2) * T * ((j + 1 : ℕ) : ℝ) * v)) ^ (j + 1) with hn0
  have hn : n0 * (j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1) =
      κ / (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1) := by
    rw [hn0, hκ]
    simp only [div_pow, mul_pow]
    field_simp
  have CP := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.constProduct j r T T' g v n0 κ dimpi Vd VV hT hT' hg hv hVV hn
  have TF := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.tcritForm (j + 1) r T' g v (2 * v) Vd VV Tc hT' hg hv (by positivity)
    hVd hVV hTc hdef
  rw [hM2] at CP
  rw [hM1] at TF ⊢
  set w : ℝ := 2 * v with hw
  have hw0 : 0 < w := by positivity
  set H : ℝ := w ^ (((2 * r + 1 : ℕ) : ℝ) / 2) with hH
  have hH0 : 0 < H := Real.rpow_pos_of_pos hw0 _
  have hHH : H * H = w ^ (2 * r + 1) := by
    rw [hH, ← Real.rpow_add hw0, ← Real.rpow_natCast]; congr 1; ring
  have hH' : w ^ ((r : ℝ) + 1 / 2) = H := by rw [hH]; congr 1; push_cast; ring
  have hgp : (g / (Real.pi / v)) ^ (2 * r ^ 2 + r + (2 * r + 1)) *
      (2 * Real.pi) ^ (2 * r ^ 2 + r + (2 * r + 1)) =
      g ^ (2 * r ^ 2 + r + (2 * r + 1)) * (w ^ (2 * r ^ 2 + r) * (H * H)) := by
    rw [hHH, ← pow_add, ← mul_pow, ← mul_pow]; congr 1; rw [hw]; field_simp
  rw [hH']
  set Q : ℝ := (Tc / T')⁻¹ ^ (j + 1) with hQ
  set G1 : ℝ := (g / (Real.pi / v)) ^ (2 * r ^ 2 + r + (2 * r + 1)) with hG1
  set Pp : ℝ := (2 * Real.pi) ^ (2 * r ^ 2 + r + (2 * r + 1)) with hPp
  set c1 : ℝ := ((2 : ℝ) ^ (r + 1))⁻¹ with hc1
  set c2 : ℝ := (th ^ (2 * r))⁻¹ with hc2
  have hwb : 0 < w ^ (2 * r ^ 2 + r) := by positivity
  calc _ = c1 * c2 * (T * T') / w ^ (2 * r ^ 2 + r) *
        (n0 * (T * T') ^ j *
          (dimpi * (Vd / ∏ i ∈ range (j + 1), (i.factorial : ℝ)) * volU (j + 1 + (2 * r + 1)) * volU j /
            (VV / (∏ i ∈ range (j + 1 + (2 * r + 1)), (i.factorial : ℝ)) * volU (j + 1) ^ 2 *
              w ^ (2 * r * (j + 1))))) := by
        rw [add_assoc (2 * r * (j + 1)), pow_add w, pow_succ (T * T')]
        ring
    _ = c1 * c2 * (T * T') / w ^ (2 * r ^ 2 + r) *
        (dimpi * (Q * (G1 / H)) * (κ * Pp / (T * T'))) := by
        rw [CP, mul_assoc dimpi, TF]
    _ = c1 * c2 * dimpi * Q * κ * (G1 * Pp) / (w ^ (2 * r ^ 2 + r) * H) := by
        field_simp
    _ = _ := by
        rw [hgp]; field_simp
end Formalism.HermitianLatticeCounting.P
