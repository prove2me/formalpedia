-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.map_of_isBaseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4a3eb143-ae22-5f0e-8e30-5bd5574c83d2

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_map_of_isBaseChangeAlong

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.FormalOmega.DrinfeldDatum TensorProduct

noncomputable section

namespace P2mKcQuadrupleNat

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']

section LocMap

variable (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B')

def locMap : locRing B (pointUnder f x') →ₐ[𝒪] locRing B' x' :=
  Localization.localAlgHom (pointUnder f x').asIdeal x'.asIdeal f rfl

theorem locMap_algebraMap (b : B) :
    locMap f x' (algebraMap B (locRing B (pointUnder f x')) b) = algebraMap B' (locRing B' x') (f b) := by
  rw [locMap, Localization.localAlgHom_apply]
  exact Localization.localRingHom_to_map _ _ _ rfl b

theorem toLocRing_comp : (toLocRing B' x').comp f = (locMap f x').comp (toLocRing B (pointUnder f x')) := by
  apply AlgHom.ext
  intro b
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  show algebraMap B' (locRing B' x') (f b) = locMap f x' (algebraMap B (locRing B (pointUnder f x')) b)
  rw [locMap_algebraMap]

theorem locMap_mk (b : B) (s : (pointUnder f x').asIdeal.primeCompl) :
    locMap f x' (Localization.mk b s) = Localization.mk (f b) (⟨f s, s.2⟩ : x'.asIdeal.primeCompl) := by
  rw [locMap, Localization.localAlgHom_apply, Localization.mk_eq_mk', Localization.localRingHom_mk',
    Localization.mk_eq_mk']
  rfl

end LocMap

section StalkMap

variable (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B')
variable {T : Type} [AddCommGroup T] [Module B T] {T' : Type} [AddCommGroup T'] [Module B' T']
variable (τ : T →ₛₗ[(f : B →+* B')] T')

theorem τ_smul (b : B) (t : T) : τ (b • t) = f b • τ t := LinearMap.map_smulₛₗ τ b t

theorem stalkMap_wd (p p' : T × (pointUnder f x').asIdeal.primeCompl) (h : p ≈ p') :
    (LocalizedModule.mk (τ p.1) (⟨f p.2, p.2.2⟩ : x'.asIdeal.primeCompl) : stalk B' x' T') =
      LocalizedModule.mk (τ p'.1) (⟨f p'.2, p'.2.2⟩ : x'.asIdeal.primeCompl) := by
  obtain ⟨u, hu⟩ := h
  rw [LocalizedModule.mk_eq]
  refine ⟨⟨f u, u.2⟩, ?_⟩
  have hu' := congrArg τ hu
  simp only [Submonoid.smul_def, τ_smul] at hu'
  simp only [Submonoid.smul_def]
  exact hu'

def stalkMap (m : stalk B (pointUnder f x') T) : stalk B' x' T' :=
  m.liftOn (fun p => LocalizedModule.mk (τ p.1) (⟨f p.2, p.2.2⟩ : x'.asIdeal.primeCompl)) (stalkMap_wd f x' τ)

theorem stalkMap_mk (t : T) (s : (pointUnder f x').asIdeal.primeCompl) :
    stalkMap f x' τ (LocalizedModule.mk t s) = LocalizedModule.mk (τ t) (⟨f s, s.2⟩ : x'.asIdeal.primeCompl) :=
  LocalizedModule.liftOn_mk _ t s

theorem stalkMap_zero : stalkMap f x' τ 0 = 0 := by
  rw [← LocalizedModule.zero_mk 1, stalkMap_mk, map_zero, LocalizedModule.zero_mk]

theorem stalkMap_add (m m' : stalk B (pointUnder f x') T) :
    stalkMap f x' τ (m + m') = stalkMap f x' τ m + stalkMap f x' τ m' := by
  induction m using LocalizedModule.induction_on with
  | h t s =>
    induction m' using LocalizedModule.induction_on with
    | h t' s' =>
      rw [LocalizedModule.mk_add_mk, stalkMap_mk, stalkMap_mk, stalkMap_mk, LocalizedModule.mk_add_mk, map_add]
      simp only [Submonoid.smul_def, τ_smul]
      congr 1
      exact Subtype.ext (by simp only [Submonoid.coe_mul, map_mul])

theorem stalkMap_smul (r : locRing B (pointUnder f x')) (m : stalk B (pointUnder f x') T) :
    stalkMap f x' τ (r • m) = locMap f x' r • stalkMap f x' τ m := by
  induction m using LocalizedModule.induction_on with
  | h t s =>
    induction r using Localization.induction_on with
    | H y =>
      obtain ⟨b, s'⟩ := y
      rw [LocalizedModule.mk_smul_mk, stalkMap_mk, stalkMap_mk, locMap_mk, LocalizedModule.mk_smul_mk, τ_smul]
      congr 1
      exact Subtype.ext (by simp only [Submonoid.coe_mul, map_mul])

theorem exists_mk {C : Type} [CommRing C] {S : Submonoid C} {M : Type} [AddCommGroup M] [Module C M]
    (m : LocalizedModule S M) : ∃ (t : M) (s : S), LocalizedModule.mk t s = m := by
  induction m using LocalizedModule.induction_on with
  | h t s => exact ⟨t, s, rfl⟩

end StalkMap

section Kernel

variable (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B')

theorem map_map_toLocRing (d : DeligneDatum (K := K) π B) :
    (d.map π f).map π (toLocRing B' x') = (d.map π (toLocRing B (pointUnder f x'))).map π (locMap f x') := by
  have h1 := (Omega K π).map_comp f (toLocRing B' x') d
  have h2 := (Omega K π).map_comp (toLocRing B (pointUnder f x')) (locMap f x') d
  change DeligneDatum.map π ((toLocRing B' x').comp f) d = (d.map π f).map π (toLocRing B' x') at h1
  change DeligneDatum.map π ((locMap f x').comp (toLocRing B (pointUnder f x'))) d =
    (d.map π (toLocRing B (pointUnder f x'))).map π (locMap f x') at h2
  rw [← h1, ← h2, toLocRing_comp]

variable {N N' : Submodule 𝒪 (Fin 2 → K)} (hN : IsFullLattice N) (hN' : IsFullLattice N')
variable {T : Type} [AddCommGroup T] [Module B T] {T' : Type} [AddCommGroup T'] [Module B' T']
variable [Module.Invertible B T] [Module.Invertible B' T']
variable (τ : T →ₛₗ[(f : B →+* B')] T')
variable (u : latticeBaseChange 𝒪 K (locRing B (pointUnder f x')) ⟨N, hN⟩ →ₗ[locRing B (pointUnder f x')]
  stalk B (pointUnder f x') T)
variable (u' : latticeBaseChange 𝒪 K (locRing B' x') ⟨N', hN'⟩ →ₗ[locRing B' x'] stalk B' x' T')

abbrev Tr (hNN' : N = N') :
    latticeBaseChange 𝒪 K (locRing B' x') ⟨N, hN⟩ ≃ₗ[locRing B' x'] latticeBaseChange 𝒪 K (locRing B' x') ⟨N', hN'⟩ :=
  transportEquiv (locRing B' x') (M₁ := ⟨N, hN⟩) (M₂ := ⟨N', hN'⟩) hNN'

abbrev rT : latticeBaseChange 𝒪 K (locRing B (pointUnder f x')) ⟨N, hN⟩ →ₗ[𝒪]
    latticeBaseChange 𝒪 K (locRing B' x') ⟨N, hN⟩ :=
  LinearMap.rTensor (↥N) (locMap f x').toLinearMap

theorem comm_all (hNN' : N = N')
    (hu : ∀ (v : Fin 2 → K) (hv : v ∈ N) (hv' : v ∈ N') (t : T) (s : B) (hs : f s ∉ x'.asIdeal),
      u ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥N)) =
        LocalizedModule.mk t (⟨s, hs⟩ : (pointUnder f x').asIdeal.primeCompl) →
      u' ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥N')) = LocalizedModule.mk (τ t) (⟨f s, hs⟩ : x'.asIdeal.primeCompl))
    (z : latticeBaseChange 𝒪 K (locRing B (pointUnder f x')) ⟨N, hN⟩) :
    u' (Tr x' hN hN' hNN' (rT f x' hN z)) = stalkMap f x' τ (u z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.map_zero, stalkMap_zero]
  | add a b ha hb =>
    rw [LinearMap.map_add, LinearEquiv.map_add, LinearMap.map_add, LinearMap.map_add, stalkMap_add, ha, hb]
  | tmul r v =>
    obtain ⟨t, s, hts⟩ := exists_mk (u ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] v))
    have hv' : (v : Fin 2 → K) ∈ N' := hNN' ▸ v.2
    have hs : f (s : B) ∉ x'.asIdeal := s.2
    have key := hu v v.2 hv' t s hs (by rw [← hts])

    have hl : Tr x' hN hN' hNN' (rT f x' hN (r ⊗ₜ[𝒪] v)) =
        locMap f x' r • ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨(v : Fin 2 → K), hv'⟩ : ↥N')) := by
      rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, transportEquiv_tmul]
      have hofEq : (LinearEquiv.ofEq _ _ hNN' v : ↥(⟨N', hN'⟩ : FullLattice 𝒪 K).1) = ⟨(v : Fin 2 → K), hv'⟩ :=
        Subtype.ext rfl
      rw [hofEq, smul_tmul', smul_eq_mul, mul_one]
    have hr : (r ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K (locRing B (pointUnder f x')) ⟨N, hN⟩) =
        r • ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] v) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [hl, map_smul, hr, map_smul, stalkMap_smul, ← hts, stalkMap_mk, key]

theorem ker_transfer (hNN' : N = N') (hu'surj : Function.Surjective u') (husurj : Function.Surjective u)
    (hu : ∀ (v : Fin 2 → K) (hv : v ∈ N) (hv' : v ∈ N') (t : T) (s : B) (hs : f s ∉ x'.asIdeal),
      u ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥N)) =
        LocalizedModule.mk t (⟨s, hs⟩ : (pointUnder f x').asIdeal.primeCompl) →
      u' ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥N')) = LocalizedModule.mk (τ t) (⟨f s, hs⟩ : x'.asIdeal.primeCompl))
    (d : DeligneDatum (K := K) π B)
    (hker : LinearMap.ker u = (d.map π (toLocRing B (pointUnder f x'))).line ⟨N, hN⟩) :
    LinearMap.ker u' = ((d.map π f).map π (toLocRing B' x')).line ⟨N', hN'⟩ := by

  have hRHS : ((d.map π f).map π (toLocRing B' x')).line ⟨N', hN'⟩ =
      (lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u)).map (Tr x' hN hN' hNN').toLinearMap := by
    have h1 := DeligneDatum.line_transport π ((d.map π f).map π (toLocRing B' x')) (M₁ := ⟨N, hN⟩) (M₂ := ⟨N', hN'⟩) hNN'
    rw [h1, map_map_toLocRing π f x' d, hker]
    rfl

  have hcomm : ∀ z, (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) (rT f x' hN z) = stalkMap f x' τ (u z) :=
    fun z => comm_all f x' hN hN' τ u u' hNN' hu z

  have hle : lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u) ≤
      LinearMap.ker (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) := by
    rw [lineBaseChange, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hz' : u z = 0 := hz
    have := hcomm z
    rw [hz', stalkMap_zero] at this
    exact this

  have hInvQ : Module.Invertible (locRing B (pointUnder f x'))
      (latticeBaseChange 𝒪 K (locRing B (pointUnder f x')) ⟨N, hN⟩ ⧸ LinearMap.ker u) :=
    Module.Invertible.congr (u.quotKerEquivOfSurjective husurj).symm
  haveI hInv' : Module.Invertible (locRing B' x')
      (latticeBaseChange 𝒪 K (locRing B' x') ⟨N, hN⟩ ⧸ lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u)) :=
    invertible_quotient_lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u) hInvQ
  have hsurj'' : Function.Surjective (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) := by
    intro m
    obtain ⟨z, rfl⟩ := hu'surj m
    exact ⟨(Tr x' hN hN' hNN').symm z, by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]⟩
  have hbij : Function.Bijective
      ((lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u)).liftQ (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) hle) := by
    apply Module.Invertible.bijective_of_surjective
    intro m
    obtain ⟨z, rfl⟩ := hsurj'' m
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hge : LinearMap.ker (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) ≤
      lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u) := by
    have h1 := LinearMap.ker_eq_bot_of_injective hbij.injective
    rw [Submodule.ker_liftQ] at h1
    have h2 := (LinearMap.le_ker_iff_map).mpr h1
    rwa [Submodule.ker_mkQ] at h2
  have hker'' : LinearMap.ker (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) =
      lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u) := le_antisymm hge hle

  rw [hRHS, ← hker'', LinearMap.ker_comp, Submodule.map_comap_eq_of_surjective]
  exact (Tr x' hN hN' hNN').surjective

end Kernel

theorem edgeNondegAt_map (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B') (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K)
    (h : d.EdgeNondegAt π (pointUnder f x').asIdeal M' M) : (d.map π f).EdgeNondegAt π x'.asIdeal M' M := by
  obtain ⟨hle, hπ, h1, h2⟩ := h
  refine ⟨hle, hπ, fun v hv => ?_, fun v' hv' => ?_⟩
  · rw [← rTensor_one_tmul f M v]
    exact rTensor_not_mem_lineBaseChange_sup f M (d.line M) (d.invertible M) x'.asIdeal _ (h1 v hv)
  · rw [← rTensor_one_tmul f M' v']
    exact rTensor_not_mem_lineBaseChange_sup f M' (d.line M') (d.invertible M') x'.asIdeal _ (h2 v' hv')

end P2mKcQuadrupleNat

end

open P2mKcQuadrupleNat in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' : DrinfeldDatum (K := K) π B'} {d : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (hf : Q.IsBaseChangeAlong f Q') : Q'.IsQuadrupleOf (d.map π f) := by
  obtain ⟨β⟩ := hf
  intro x'
  obtain ⟨hedge, hk₀, hk₁⟩ := h (pointUnder f x')
  have hL₀ : Q'.L₀ x' = Q.L₀ (pointUnder f x') := Subtype.ext (β.N₀_eq x')
  have hL₁ : Q'.L₁ x' = Q.L₁ (pointUnder f x') := Subtype.ext (β.N₁_eq x')
  refine ⟨?_, ?_, ?_⟩
  · rw [hL₀, hL₁]; exact edgeNondegAt_map π f x' d _ _ hedge
  · exact ker_transfer π f x' (Q.full₀ (pointUnder f x')) (Q'.full₀ x') β.τ₀
      (Q.u₀ (pointUnder f x')) (Q'.u₀ x') (β.N₀_eq x').symm (Q'.u₀_surjective x') (Q.u₀_surjective _)
      (fun v hv hv' t s hs => β.u₀_eq x' v hv hv' t s hs) d hk₀
  · exact ker_transfer π f x' (Q.full₁ (pointUnder f x')) (Q'.full₁ x') β.τ₁
      (Q.u₁ (pointUnder f x')) (Q'.u₁ x') (β.N₁_eq x').symm (Q'.u₁_surjective x') (Q.u₁_surjective _)
      (fun v hv hv' t s hs => β.u₁_eq x' v hv hv' t s hs) d hk₁

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_map_of_isBaseChangeAlong
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_map_of_isBaseChangeAlong (solution)
