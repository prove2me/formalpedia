-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crIsMono_pow
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T09:42:20.091874+00:00
-- url     : https://prove2.me/submissions/ca1282e0-1c56-4abd-b0e2-834fe6e59889

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin

noncomputable section

open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial

variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}

theorem solution {R : Type} [CommRing R] {p : MvPolynomial (Letter T r n) R} (hp : crIsMono p)
    (e : ℕ) : crIsMono (p ^ e) := by
  obtain ⟨E, hE⟩ := hp
  use e • E
  rw [hE, monomial_pow]
  simp
