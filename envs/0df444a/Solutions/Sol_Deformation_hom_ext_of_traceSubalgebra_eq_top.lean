-- Prove2me | solution 1 for Deformation.hom_ext_of_traceSubalgebra_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e69e1792-898a-541d-a42d-ef651c833de1

import Mathlib
import Definitions.Def_Deformations_TraceAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_hom_ext_of_traceSubalgebra_eq_top

open CategoryTheory

universe u

theorem solution {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] {A B : Deformation.ProartinianCat 𝓞} {f g : A ⟶ B} {σ : G →ₜ* GL n A}
    (hσ : Deformation.traceSubalgebra 𝓞 σ = ⊤)
    (h : ∀ x : G, f.hom (Matrix.trace ((σ x : GL n A) : Matrix n n A)) =
      g.hom (Matrix.trace ((σ x : GL n A) : Matrix n n A))) : f = g := by

  have hle : Deformation.traceSubalgebra 𝓞 σ ≤ AlgHom.equalizer f.hom.toAlgHom g.hom.toAlgHom :=
    Deformation.traceSubalgebra_le σ (isClosed_eq f.hom.cont g.hom.cont) h
  refine Deformation.ProartinianCat.hom_ext (ContinuousAlgHom.ext fun a => ?_)
  exact hle (hσ.ge (Algebra.mem_top (R := 𝓞) (A := A.carrier) (x := a)))

end S_Deformation_hom_ext_of_traceSubalgebra_eq_top
end P2MW
export P2MW.S_Deformation_hom_ext_of_traceSubalgebra_eq_top (solution)
