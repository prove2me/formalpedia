-- Prove2me | solution 2 for DiazModulus.candidate_vanishing_ideal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:19:06.509987+00:00
-- url     : https://prove2.me/submissions/f1172d59-26e3-4506-bb5e-d62cdc6868a0

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Transcendence_circle_vanishing_ideal
import Theorems.Thm_DiazModulus_candidate_im_transcendental

namespace S7W1_candidate_vanishing_ideal

open DiazModulus

/-- `Q̄` is algebraic over `ℚ`, so transcendence over `ℚ` lifts to `Q̄`. -/
instance : Algebra.IsAlgebraic ℚ Qbar :=
  ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩

end S7W1_candidate_vanishing_ideal

-- `(Re u, Im u)` lies on the circle `x² + y² = ‖u‖²` and `Im u` is transcendental over `Q̄`
-- (`candidate_im_transcendental`), so `Transcendence.circle_vanishing_ideal` applies.
open Complex DiazModulus S7W1_candidate_vanishing_ideal in
theorem solution (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u)
    (P : MvPolynomial (Fin 2) (↥Qbar)) :
    MvPolynomial.aeval
        (fun i : Fin 2 => if i = 0 then ((u.re : ℝ) : ℂ) else ((u.im : ℝ) : ℂ)) P = 0 ↔
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 -
          MvPolynomial.C ⟨((‖u‖ : ℝ) : ℂ) ^ 2,
            Subfield.pow_mem (s := Qbar) (mem_Qbar_iff.mpr h.2.1) 2⟩) ∣ P := by
  have hpt : (fun i : Fin 2 => if i = 0 then ((u.re : ℝ) : ℂ) else ((u.im : ℝ) : ℂ)) =
      ![((u.re : ℝ) : ℂ), ((u.im : ℝ) : ℂ)] := by
    funext i; fin_cases i <;> simp
  rw [hpt]
  refine Transcendence.circle_vanishing_ideal (fun h0 => h.1 ?_) ?_
    ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).mp (candidate_im_transcendental hHL h)) P
  · simpa using congrArg Subtype.val h0
  · show _ = ((‖u‖ : ℝ) : ℂ) ^ 2
    have : u.re ^ 2 + u.im ^ 2 = ‖u‖ ^ 2 := by rw [← normSq_eq_norm_sq, normSq_apply]; ring
    exact_mod_cast this

#print axioms solution
