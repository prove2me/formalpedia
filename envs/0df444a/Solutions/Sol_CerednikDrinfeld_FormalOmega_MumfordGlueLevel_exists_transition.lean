-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/34985cba-38ed-54e4-967b-a5eff87fa9f1

import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_alpha_eq_alpha_comp_factor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_tau_eq_tau_comp_factor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_iota_eq_iota_comp_factor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_isPullback_zb_of_forall_zeta_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_exists_transition
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀))) (n : ℕ)
    (L : MumfordGlueLevel 𝒪 π K₀ r g₁ N n) (L' : MumfordGlueLevel 𝒪 π K₀ r g₁ N (n + 1)) :
    ∃ zt : L.Z ⟶ L'.Z,
      IsPullback zt L.zb L'.zb
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) ∧
      ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀,
        L.ζ h ≫ zt = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1)))))) ≫ L'.ζ h := by

  let SA := Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1))))))
  let SV := Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartVRing 𝒪 r) π) (Nat.le_succ (n + 1))))))

  have eι : Spec.map (CommRingCat.ofHom L.ι.toRingHom) ≫ SA = SV ≫ Spec.map (CommRingCat.ofHom L'.ι.toRingHom) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      MumfordGlueLevel.factor_comp_iota_eq_iota_comp_factor 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N n L L']
  have eα : ∀ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
      ((Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
        (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀))) →
      Spec.map (CommRingCat.ofHom (L.α g).toAlgHom.toRingHom) ≫ SA = SA ≫ Spec.map (CommRingCat.ofHom (L'.α g).toAlgHom.toRingHom) := by
    intro g hg
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      MumfordGlueLevel.factor_comp_alpha_eq_alpha_comp_factor 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N n L L' g hg]
  have eτ : ∀ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) →
      Spec.map (CommRingCat.ofHom (L.τ g).toAlgHom.toRingHom) ≫ SV = SV ≫ Spec.map (CommRingCat.ofHom (L'.τ g).toAlgHom.toRingHom) := by
    intro g hg
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      MumfordGlueLevel.factor_comp_tau_eq_tau_comp_factor 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N n L L' g hg]

  obtain ⟨zt, hzt, -⟩ := L.desc L'.Z (fun h => SA ≫ L'.ζ h)
    (fun g h hg => by show SA ≫ L'.ζ (g * h) = SA ≫ L'.ζ h; rw [L'.ζ_inv g h hg])
    (fun h g hg => by
      show SA ≫ L'.ζ (h * g) = Spec.map (CommRingCat.ofHom (L.α g).toAlgHom.toRingHom) ≫ SA ≫ L'.ζ h
      rw [L'.ζ_edge h g hg, ← Category.assoc, ← Category.assoc, eα g hg])
    (fun h g hg => by
      show Spec.map (CommRingCat.ofHom L.ι.toRingHom) ≫ SA ≫ L'.ζ (h * g) =
        Spec.map (CommRingCat.ofHom (L.τ g).toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom L.ι.toRingHom) ≫ SA ≫ L'.ζ h
      rw [← Category.assoc, eι, Category.assoc, L'.ζ_vertex h g hg, ← Category.assoc, ← eτ g hg, Category.assoc,
        ← Category.assoc (Spec.map (CommRingCat.ofHom L.ι.toRingHom)), eι, Category.assoc])
  exact ⟨zt, MumfordGlueLevel.isPullback_zb_of_forall_zeta_comp_eq 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N n L L' zt hzt, hzt⟩

end S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_exists_transition
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_exists_transition (solution)
