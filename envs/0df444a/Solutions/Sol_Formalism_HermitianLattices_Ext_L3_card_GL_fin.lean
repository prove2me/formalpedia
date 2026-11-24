-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.card_GL_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:40.46572+00:00
-- url     : https://prove2.me/submissions/c3b19b8c-7198-4ece-b678-364ed2354eb4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution {k : Type*} [Field k] [Fintype k] (q : ℕ) (hq : Fintype.card k = q) (m : ℕ) :
    (Nat.card (GL (Fin m) k) : ℝ) = (q : ℝ) ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (1 - (q : ℝ)⁻¹ ^ j) := by
  subst hq
  set q : ℕ := Fintype.card k with hqd
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hq0 : (q : ℝ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  rw [Matrix.card_GL_field, Fin.prod_univ_eq_prod_range (fun i => q ^ m - q ^ i) m, Nat.cast_prod]
  have h1 : ∀ i ∈ Finset.range m, ((q ^ m - q ^ i : ℕ) : ℝ) =
      (q : ℝ) ^ m * (1 - (q : ℝ)⁻¹ ^ (m - 1 - i + 1)) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq1 him.le), Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
    congr 1
    have : m = i + (m - 1 - i + 1) := by omega
    conv_rhs => rw [this, pow_add]
    have h5 : m - 1 - i + 1 = i + (m - 1 - i + 1) - 1 - i + 1 := by omega
    rw [← h5, mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, mul_one]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul, ← sq, Finset.prod_range_reflect (fun j => 1 - (q : ℝ)⁻¹ ^ (j + 1)) m]
  congr 1
  rw [Finset.range_eq_Ico, Finset.prod_Ico_add' (fun j => 1 - (q : ℝ)⁻¹ ^ j) 0 m 1]
  rfl
end Formalism.HermitianLattices.Ext.L3
