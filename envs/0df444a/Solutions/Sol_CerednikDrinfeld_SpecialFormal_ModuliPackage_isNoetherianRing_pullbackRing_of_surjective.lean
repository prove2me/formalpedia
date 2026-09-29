-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.isNoetherianRing_pullbackRing_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/5ecfa5a7-c14f-5cfb-a540-b22b4b0a536f

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_isNoetherianRing_pullbackRing_of_surjective

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage

namespace NoethPullbackAux

theorem isNoetherian_compHom {R S M : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M]
    (f : R →+* S) (hf : Function.Surjective f) [IsNoetherian S M] :
    @IsNoetherian R M _ _ (Module.compHom M f) := by
  letI : Module R M := Module.compHom M f
  rw [isNoetherian_def]
  intro N

  let N' : Submodule S M :=
    { carrier := N
      zero_mem' := N.zero_mem
      add_mem' := fun ha hb => N.add_mem ha hb
      smul_mem' := fun s x hx => by
        obtain ⟨r, rfl⟩ := hf s
        exact N.smul_mem r hx }
  obtain ⟨t, ht⟩ := (isNoetherian_def.mp inferInstance) N'
  refine ⟨t, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro x hx
    have : x ∈ N' := ht ▸ Submodule.subset_span hx
    exact this
  · intro x hx
    have hx' : x ∈ Submodule.span S (t : Set M) := ht.symm ▸ (show x ∈ N' from hx)
    refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span R (t : Set M)) ?_ ?_ ?_ ?_ hx'
    · intro y hy; exact Submodule.subset_span hy
    · exact Submodule.zero_mem _
    · intro y z _ _ hy hz; exact Submodule.add_mem _ hy hz
    · intro s y _ hy
      obtain ⟨r, rfl⟩ := hf s
      exact Submodule.smul_mem _ r hy

end NoethPullbackAux

open NoethPullbackAux in

theorem noethPullback {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B'] [IsNoetherianRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : Function.Surjective φ') (hφ'' : Function.Surjective φ'') :
    IsNoetherianRing (pullbackRing φ' φ'') := by
  classical
  let P := pullbackRing φ' φ''

  have hfst : Function.Surjective (pullbackFst φ' φ'') := by
    intro b'
    obtain ⟨b'', hb''⟩ := hφ'' (φ' b')
    exact ⟨⟨(b', b''), hb''.symm⟩, rfl⟩
  have hsnd : Function.Surjective (pullbackSnd φ' φ'') := by
    intro b''
    obtain ⟨b', hb'⟩ := hφ' (φ'' b'')
    exact ⟨⟨(b', b''), hb'⟩, rfl⟩

  letI mB' : Module P B' := Module.compHom B' (pullbackFst φ' φ'')
  letI mB'' : Module P B'' := Module.compHom B'' (pullbackSnd φ' φ'')
  haveI : IsNoetherian P B' := isNoetherian_compHom (pullbackFst φ' φ'') hfst
  haveI : IsNoetherian P B'' := isNoetherian_compHom (pullbackSnd φ' φ'') hsnd

  let g : P →ₗ[P] B' :=
    { toFun := fun z => z.1.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let K : Submodule P P := LinearMap.ker g

  let j : K →ₗ[P] B'' :=
    { toFun := fun k => k.1.1.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro k k' h
    have h1 : k.1.1.1 = 0 := k.2
    have h1' : k'.1.1.1 = 0 := k'.2
    exact Subtype.ext (Subtype.ext (Prod.ext (h1.trans h1'.symm) h))
  haveI : IsNoetherian P K := isNoetherian_of_injective j hj
  have hP : IsNoetherian P P := isNoetherian_of_range_eq_ker K.subtype g (by rw [Submodule.range_subtype])
  exact hP

theorem solution
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B'] [IsNoetherianRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : Function.Surjective φ') (hφ'' : Function.Surjective φ'') :
    IsNoetherianRing (ModuliPackage.pullbackRing φ' φ'') :=
  noethPullback φ' φ'' hφ' hφ''

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_isNoetherianRing_pullbackRing_of_surjective
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_isNoetherianRing_pullbackRing_of_surjective (solution)
