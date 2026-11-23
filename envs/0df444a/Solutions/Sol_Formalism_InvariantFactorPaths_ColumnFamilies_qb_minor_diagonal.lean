-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_minor_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:50.337802+00:00
-- url     : https://prove2.me/submissions/e185e4e5-662c-466e-a748-5ef15d74077b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] (d : Fin n → R) {h : ℕ} (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    Matrix.det (Matrix.of fun a b : Fin h => Matrix.diagonal d (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) =
      if J = I then ∏ x ∈ J, d x else 0 := by
  split_ifs with hJI
  · subst hJI
    have : (Matrix.of fun a b : Fin h => Matrix.diagonal d (J.orderEmbOfFin hJ a) (J.orderEmbOfFin hI b)) =
        Matrix.diagonal fun a => d (J.orderEmbOfFin hJ a) := by
      ext a b
      simp [Matrix.diagonal_apply]
    rw [this, Matrix.det_diagonal]
    conv_rhs => rw [← map_orderEmbOfFin_univ J hJ]
    rw [prod_map]
    rfl
  · have : ∃ x ∈ J, x ∉ I := by
      by_contra hc
      push Not at hc
      exact hJI (eq_of_subset_of_card_le hc (by rw [hJ, hI]))
    obtain ⟨x, hxJ, hxI⟩ := this
    rw [← map_orderEmbOfFin_univ J hJ, mem_map] at hxJ
    obtain ⟨a, -, rfl⟩ := hxJ
    apply Matrix.det_eq_zero_of_row_eq_zero a
    intro b
    rw [Matrix.of_apply, Matrix.diagonal_apply_ne]
    intro hab
    apply hxI
    have := orderEmbOfFin_mem I hI b
    rw [← hab] at this
    exact this
end Formalism.InvariantFactorPaths.ColumnFamilies
