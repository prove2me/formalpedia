-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.q_roots_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:18.88644+00:00
-- url     : https://prove2.me/submissions/90689207-0538-4ce7-89fd-ae3fae83d5bc

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_X_mul_q_eq_one_add_X_pow_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : QRoots := by
  intro l _ O _ _ _ ζ hζ
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hlpos : 0 < l := (Fact.out : l.Prime).pos
  have h1 : (Polynomial.X ^ l - 1 : Polynomial O) =
      ∏ b ∈ Finset.range l, (Polynomial.X - Polynomial.C (ζ ^ b)) := by
    rw [Polynomial.X_pow_sub_one_eq_prod hlpos hζ]
    symm
    apply Finset.prod_nbij (fun b => ζ ^ b)
    · intro b _
      rw [Polynomial.mem_nthRootsFinset hlpos, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · intro b hb b' hb' h
      exact hζ.pow_inj (Finset.mem_range.mp hb) (Finset.mem_range.mp hb') h
    · intro ξ hξ
      obtain ⟨i, hi, hiξ⟩ := hζ.eq_pow_of_pow_eq_one
        ((Polynomial.mem_nthRootsFinset hlpos _).mp hξ)
      exact ⟨i, Finset.mem_coe.mpr (Finset.mem_range.mpr hi), hiξ⟩
    · intro b _; rfl
  have h2 := congrArg (Polynomial.eval₂RingHom (C : O →+* O⟦X⟧) (1 + X)) h1
  simp only [map_sub, map_pow, map_one, map_prod, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at h2
  have h3 : (Finset.range l).erase 0 = Finset.Ioo 0 l := by
    ext b; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ioo]; omega
  rw [← Finset.mul_prod_erase (Finset.range l) _ (Finset.mem_range.mpr hlpos), h3,
    ← X_mul_q_eq_one_add_X_pow_sub_one l O] at h2
  have h4 : (1 + X - (C ζ) ^ 0 : O⟦X⟧) = X := by simp
  rw [h4] at h2
  have h5 := mul_left_cancel₀ (X_ne_zero (R := O)) h2
  rw [h5]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [map_sub, map_pow, map_one]
  ring
end Formalism.CohomologicalDescent.HeightDescentMinors
