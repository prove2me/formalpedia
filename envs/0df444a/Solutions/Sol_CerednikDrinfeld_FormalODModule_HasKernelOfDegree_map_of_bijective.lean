-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.HasKernelOfDegree.map_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/940d6745-67d6-535d-8797-67c3e3bb0af9

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective

set_option autoImplicit false

universe u

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective.CerednikDrinfeld CerednikDrinfeld.SpecialFormal"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalODModule FormalODModule.KerAlgebra FormalODModule.HasKernelOfDegree"
namespace FormalODModule
p2m_export "CerednikDrinfeld.FormalODModule" "map map_map KerAlgebra HasKernelOfDegree F mk"
namespace KerTransport
p2m_open "CerednikDrinfeld.FormalODModule CerednikDrinfeld"

variable {B B' : Type u} [CommRing B] [CommRing B'] (e : B ≃+* B')

noncomputable def seriesEquiv : MvPowerSeries (Fin 2) B ≃+* MvPowerSeries (Fin 2) B' :=
  { MvPowerSeries.map (σ := Fin 2) (e : B →+* B') with
    invFun := MvPowerSeries.map (σ := Fin 2) (e.symm : B' →+* B)
    left_inv := fun x => by
      show MvPowerSeries.map (σ := Fin 2) (e.symm : B' →+* B) (MvPowerSeries.map (σ := Fin 2) (e : B →+* B') x) = x
      ext n
      rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
      exact e.symm_apply_apply _
    right_inv := fun x => by
      show MvPowerSeries.map (σ := Fin 2) (e : B →+* B') (MvPowerSeries.map (σ := Fin 2) (e.symm : B' →+* B) x) = x
      ext n
      rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
      exact e.apply_symm_apply _ }

@[scoped simp] theorem seriesEquiv_apply (x : MvPowerSeries (Fin 2) B) :
    seriesEquiv e x = MvPowerSeries.map (σ := Fin 2) (e : B →+* B') x := rfl

theorem coe_seriesEquiv :
    ((seriesEquiv e : MvPowerSeries (Fin 2) B ≃+* MvPowerSeries (Fin 2) B') : MvPowerSeries (Fin 2) B →+* _) =
      MvPowerSeries.map (σ := Fin 2) (e : B →+* B') :=
  RingHom.ext fun _ => rfl

theorem map_eq (φ : Series B) : φ.map (e : B →+* B') = fun i => seriesEquiv e (φ i) := rfl

theorem span_map (φ : Series B) :
    Ideal.span (Set.range (φ.map (e : B →+* B'))) =
      Ideal.map ((seriesEquiv e : MvPowerSeries (Fin 2) B ≃+* MvPowerSeries (Fin 2) B') : MvPowerSeries (Fin 2) B →+* _)
        (Ideal.span (Set.range φ)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

noncomputable def kerEquiv (φ : Series B) :
    FormalODModule.KerAlgebra φ ≃+* FormalODModule.KerAlgebra (φ.map (e : B →+* B')) :=
  Ideal.quotientEquiv (Ideal.span (Set.range φ)) (Ideal.span (Set.range (φ.map (e : B →+* B'))))
    (seriesEquiv e) (span_map e φ)

theorem kerEquiv_mk (φ : Series B) (x : MvPowerSeries (Fin 2) B) :
    kerEquiv e φ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (MvPowerSeries.map (σ := Fin 2) (e : B →+* B') x) :=
  Ideal.quotientEquiv_mk _ _ _ _ x

theorem kerEquiv_algebraMap (φ : Series B) (b : B) :
    kerEquiv e φ (algebraMap B (FormalODModule.KerAlgebra φ) b) =
      algebraMap B' (FormalODModule.KerAlgebra (φ.map (e : B →+* B'))) (e b) := by
  rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, kerEquiv_mk, MvPowerSeries.algebraMap_apply,
    MvPowerSeries.algebraMap_apply, MvPowerSeries.map_C]
  rfl

theorem algebraMap_comp (φ : Series B) :
    (algebraMap B' (FormalODModule.KerAlgebra (φ.map (e : B →+* B')))).comp (e : B →+* B') =
      ((kerEquiv e φ : FormalODModule.KerAlgebra φ ≃+* _) : FormalODModule.KerAlgebra φ →+* _).comp
        (algebraMap B (FormalODModule.KerAlgebra φ)) :=
  RingHom.ext fun b => (kerEquiv_algebraMap e φ b).symm

theorem kerEquiv_smul (φ : Series B) (b : B) (x : FormalODModule.KerAlgebra φ) :
    kerEquiv e φ (b • x) = e b • kerEquiv e φ x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change kerEquiv e φ (Ideal.Quotient.mk _ (b • x)) = _
  rw [kerEquiv_mk, kerEquiv_mk]
  change _ = Ideal.Quotient.mk _ ((e b) • MvPowerSeries.map (σ := Fin 2) (e : B →+* B') x)
  congr 1
  rw [MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C]
  rfl

noncomputable def kerLinearEquiv (φ : Series B) :
    letI := RingHomInvPair.of_ringEquiv e
    letI := (RingHomInvPair.of_ringEquiv e).symm
    FormalODModule.KerAlgebra φ ≃ₛₗ[(e : B →+* B')] FormalODModule.KerAlgebra (φ.map (e : B →+* B')) :=
  letI := RingHomInvPair.of_ringEquiv e
  letI := (RingHomInvPair.of_ringEquiv e).symm
  { (kerEquiv e φ).toAddEquiv with
    map_smul' := fun b x => kerEquiv_smul e φ b x }

theorem finite_map (φ : Series B) [Module.Finite B (FormalODModule.KerAlgebra φ)] :
    Module.Finite B' (FormalODModule.KerAlgebra (φ.map (e : B →+* B'))) :=
  Module.Finite.of_equiv_equiv e (kerEquiv e φ) (algebraMap_comp e φ)

theorem projective_map (φ : Series B) [Module.Projective B (FormalODModule.KerAlgebra φ)] :
    Module.Projective B' (FormalODModule.KerAlgebra (φ.map (e : B →+* B'))) := by
  letI := RingHomInvPair.of_ringEquiv e
  letI := (RingHomInvPair.of_ringEquiv e).symm
  exact Module.Projective.of_equiv (kerLinearEquiv e φ)

end CerednikDrinfeld.FormalODModule.KerTransport
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective.CerednikDrinfeld.FormalODModule P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective.CerednikDrinfeld.FormalODModule.KerTransport"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective.CerednikDrinfeld.FormalODModule"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective.CerednikDrinfeld"

open CerednikDrinfeld.FormalODModule.KerTransport in
theorem solution
    {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B') (hf : Function.Bijective f)
    {φ : Series B} {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) :
    FormalODModule.HasKernelOfDegree (φ.map f) d := by
  obtain ⟨hfin, hproj, hrank⟩ := hφ

  let e : B ≃+* B' := RingEquiv.ofBijective f hf
  have he : (e : B →+* B') = f := RingHom.ext fun _ => rfl
  refine ⟨?_, ?_, fun κ _ g => ?_⟩
  · rw [← he]; exact finite_map e φ
  · rw [← he]; exact projective_map e φ
  ·
    rw [Series.map_map]
    exact hrank κ (g.comp f)

end S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective (solution)
