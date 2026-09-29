-- Prove2me | solution 1 for Deformation.hom_ext_of_mk_mapRepn_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/110baf06-f622-50ce-a6cd-1c6a21fefe62

import Mathlib
import Definitions.Def_Deformations_TraceAlgebra
import Theorems.Thm_Deformation_hom_ext_of_traceSubalgebra_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_hom_ext_of_mk_mapRepn_eq

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false in
theorem solution {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {A B : Deformation.ProartinianCat 𝓞} {f g : A ⟶ B}
    {σ : G →ₜ* GL n A} (hσ : Deformation.traceSubalgebra 𝓞 σ = ⊤)
    (h : (Quotient.mk'' (Deformation.mapRepn n G 𝓞 f σ) : (Deformation.repnQuotFunctor n G 𝓞).obj B) =
      Quotient.mk'' (Deformation.mapRepn n G 𝓞 g σ)) : f = g := by
  rw [Quotient.eq''] at h
  obtain ⟨δ, hδ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  refine Deformation.hom_ext_of_traceSubalgebra_eq_top hσ fun x => ?_
  have hδ' : (δ : ConjAct (GL n B)) • Deformation.mapRepn n G 𝓞 g σ = Deformation.mapRepn n G 𝓞 f σ := hδ
  calc f.hom (Matrix.trace ((σ x : GL n A) : Matrix n n A))
      = Matrix.trace ((Deformation.mapRepn n G 𝓞 f σ x : GL n B) : Matrix n n B) :=
        (Deformation.trace_mapRepn f σ x).symm
    _ = Matrix.trace ((((δ : ConjAct (GL n B)) • Deformation.mapRepn n G 𝓞 g σ) x : GL n B) : Matrix n n B) := by
        rw [hδ']
    _ = Matrix.trace ((Deformation.mapRepn n G 𝓞 g σ x : GL n B) : Matrix n n B) :=
        Deformation.trace_smul_eq (δ : ConjAct (GL n B)) (Deformation.mapRepn n G 𝓞 g σ) x
    _ = g.hom (Matrix.trace ((σ x : GL n A) : Matrix n n A)) := Deformation.trace_mapRepn g σ x

end S_Deformation_hom_ext_of_mk_mapRepn_eq
end P2MW
export P2MW.S_Deformation_hom_ext_of_mk_mapRepn_eq (solution)
