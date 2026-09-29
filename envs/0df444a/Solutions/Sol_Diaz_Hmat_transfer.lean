-- Prove2me | solution 1 for Diaz.Hmat_transfer
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:29:30.715271+00:00
-- url     : https://prove2.me/submissions/75197b13-1444-4406-bc7d-f624dbcef874

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Rigidity
import Theorems.Thm_Diaz_conj_comm

namespace Diaz

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

theorem self_mem_hull : u ∈ hull K u :=
  Subfield.subset_closure (Or.inr rfl)
end

end Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u t : ℂ}

open Diaz in
theorem solution (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a) {r : ℂ} (hr : r ∈ K)
    (hKconj : ∀ a ∈ K, conj a ∈ K) (hu0 : u ≠ 0) (ht0 : t ≠ 0) (hΦu : Φ u = t)
    (hρ : u * conj u ∈ K) (hρt : t * conj t = u * conj u) :
    (Hmat u r).map Φ = Hmat t r := by
  have hc : Φ (conj u) = conj t := by
    have := conj_comm Φ hK hKconj hu0 ht0 hΦu hρ hρt u self_mem_hull
    rwa [hΦu] at this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hmat, Matrix.map_apply, hΦu, hK _ hr, hc]
end
