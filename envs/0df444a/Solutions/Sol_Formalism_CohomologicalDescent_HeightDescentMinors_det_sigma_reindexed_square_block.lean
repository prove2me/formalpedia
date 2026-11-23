-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.det_sigma_reindexed_square_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:33.919491+00:00
-- url     : https://prove2.me/submissions/d114fbae-8546-4bb3-ba2c-5ad4558fef8a

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

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
variable {R : Type} [CommRing R]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {n : ℕ} (Φ : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) (I : Finset ℕ)
    (tt : ↥I → ℕ) (F G : ∀ r : ↥I, Fin (tt r) → {j // b j = r.1}) (r : ↥I) :
    ((Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1)
        (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).toSquareBlock
          (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1) r.1).det =
      ((Φ.toSquareBlock b r.1).submatrix (F r) (G r)).det := by
  let e0 : Fin (tt r) → {y : (Σ r : ↥I, Fin (tt r)) // y.1.1 = r.1} := fun i => ⟨⟨r, i⟩, rfl⟩
  have he0 : Function.Bijective e0 := by
    constructor
    · intro i j hij
      have h1 : (⟨r, i⟩ : Σ r : ↥I, Fin (tt r)) = ⟨r, j⟩ := congrArg Subtype.val hij
      simpa using h1
    · rintro ⟨⟨r', i⟩, hy⟩
      have hr : r' = r := Subtype.ext hy
      subst hr
      exact ⟨i, rfl⟩
  rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective e0 he0)]
  rfl
end Formalism.CohomologicalDescent.HeightDescentMinors
