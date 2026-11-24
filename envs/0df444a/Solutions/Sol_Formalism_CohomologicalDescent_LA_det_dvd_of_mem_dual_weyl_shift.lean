-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.det_dvd_of_mem_dual_weyl_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:32.071912+00:00
-- url     : https://prove2.me/submissions/f10cbf80-deab-4880-886b-6e2cf978c816

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_weyl_shift_eq_map_det_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_uniform
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial
noncomputable section
namespace Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
private theorem genericDet_dvd_of_nsmul_eq_mul {r : ℕ} (N : ℕ) (hN : N ≠ 0)
    (f g : MvPolynomial (Fin r × Fin r) ℤ) (h : (N : ℤ) • f = genericDet ℤ r * g) :
    genericDet ℤ r ∣ f := by
  have hev : MvPolynomial.eval (fun v : Fin r × Fin r => if v.1 = v.2 then (1 : ℤ) else 0)
      (genericDet ℤ r) = 1 := by
    unfold genericDet
    rw [RingHom.map_det]
    have hM : (MvPolynomial.eval (fun v : Fin r × Fin r => if v.1 = v.2 then (1 : ℤ) else 0)).mapMatrix
        (genericMatrix' ℤ r) = 1 := by
      ext p q
      simp [genericMatrix', Matrix.one_apply]
    rw [hM, Matrix.det_one]
  have hnd : ∀ p : ℕ, p.Prime → ¬ (C (p : ℤ) ∣ genericDet ℤ r) := by
    rintro p hp ⟨h', hh⟩
    have he := congrArg (MvPolynomial.eval (fun v : Fin r × Fin r =>
      if v.1 = v.2 then (1 : ℤ) else 0)) hh
    rw [hev, map_mul, eval_C] at he
    have h1 : (p : ℤ) ∣ 1 := ⟨_, he⟩
    have h2 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h1
    exact hp.one_lt.ne' (by exact_mod_cast h2)
  revert f g
  refine Nat.recOnMul (motive := fun N => N ≠ 0 → ∀ f g : MvPolynomial (Fin r × Fin r) ℤ,
    (N : ℤ) • f = genericDet ℤ r * g → genericDet ℤ r ∣ f) ?_ ?_ ?_ ?_ N hN
  · intro h0
    exact absurd rfl h0
  · intro _ f g h
    rw [Nat.cast_one, one_smul] at h
    exact ⟨g, h⟩
  · intro p hp _ f g h
    have hpr : Prime (C (p : ℤ) : MvPolynomial (Fin r × Fin r) ℤ) :=
      (MvPolynomial.prime_C_iff (Fin r × Fin r)).mpr (Nat.prime_iff_prime_int.mp hp)
    rw [MvPolynomial.smul_eq_C_mul] at h
    rcases hpr.dvd_or_dvd ⟨f, h.symm⟩ with hd | ⟨g', rfl⟩
    · exact absurd hd (hnd p hp)
    · refine ⟨g', mul_left_cancel₀ hpr.ne_zero ?_⟩
      rw [h]
      ring
  · intro a b ha hb hab f g h
    have h' : (a : ℤ) • ((b : ℤ) • f) = genericDet ℤ r * g := by
      rw [smul_smul, ← Nat.cast_mul]
      exact h
    obtain ⟨g', hg'⟩ := ha (left_ne_zero_of_mul hab) _ g h'
    exact hb (right_ne_zero_of_mul hab) f g' hg'
end Formalism.CohomologicalDescent.LA
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν)
    {f : MvPolynomial (Fin r × Fin r) ℤ} (hf : f ∈ dualWeyl ℤ r r (fun a => ν a + 1)) :
    genericDet ℤ r ∣ f := by
  obtain ⟨N, hN, hNx⟩ := la_uniform r r le_rfl (fun a => ν a + 1)
    (fun a b hab => Nat.add_le_add_right (hν hab) 1)
  have hmem := hNx f hf
  rw [weyl_shift_eq_map_det_mul] at hmem
  obtain ⟨g, -, hg⟩ := Submodule.mem_map.mp hmem
  exact genericDet_dvd_of_nsmul_eq_mul N hN f g (by rw [← hg, LinearMap.mulLeft_apply])
end Formalism.CohomologicalDescent.LA
