-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_univ_law
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7fb4bc7c-c770-5a30-a27c-c7c1e4ee0646

import Mathlib
import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_univ_law
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

noncomputable section

namespace F2Beta3

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪) {B : Type} [CommRing B] [Algebra 𝒪 B]

abbrev gact (g : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) : DeligneDatum (K := K) π B :=
  DeligneDatum.pullback π B g⁻¹ d

theorem gact_mul (g h : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    gact π (g * h) d = gact π g (gact π h d) :=
  (Omega.action K π).act_mul B g h d

theorem gact_one (d : DeligneDatum (K := K) π B) : gact π 1 d = d :=
  (Omega.action K π).act_one B d

theorem isPullback_gact (g : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d (gact π g d) :=
  DeligneDatum.isPullback_pullback π B g⁻¹ d

theorem eq_gact_of_isPullback (g : GL (Fin 2) K) (d d' : DeligneDatum (K := K) π B)
    (h : DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d') : d' = gact π g d :=
  DeligneDatum.ext' (funext fun M => h M)

theorem line_edge_to_vertex (g₁ : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) (ξB ηB : B) (hu : IsUnit ξB)
    (hξη : ξB * ηB = algebraMap 𝒪 B π)
    (h2 : d.line (FullLattice.act g₁ (stdFullLattice K)) =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + ηB ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B g₁ (stdFullLattice K)).toLinearMap) :
    d.line (FullLattice.act g₁ (stdFullLattice K)) =
      (Submodule.span B {ξB ⊗ₜ[𝒪] stdBasisVec K 0 + (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B g₁ (stdFullLattice K)).toLinearMap := by
  rw [h2, ← Submodule.span_singleton_smul_eq hu (_ + _), smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    smul_eq_mul, smul_eq_mul, mul_one, hξη]

variable {r : ℕ}

omit B in

theorem isNilpotent_of_algHom {R : Type} [CommRing R] [Algebra 𝒪 R] (n : ℕ) {C : Type} [CommRing C] [Algebra 𝒪 C]
    (x : (R ⧸ Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)}) →ₐ[𝒪] C) : IsNilpotent (algebraMap 𝒪 C π) := by
  rw [← x.commutes π]
  exact (isNilpotent_algebraMap_modPow π R n).map x

theorem exists_edgeChartDatum [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) [IsFractionRing 𝒪 K]
    (g₁ : GL (Fin 2) K) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) (n : ℕ)
    {C : Type} [CommRing C] [Algebra 𝒪 C]
    (xq : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] C) :
    ∃ d : DeligneDatum (K := K) π C,
      d.line (stdFullLattice K) =
          Submodule.span C {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
            (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : C) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K)) =
          (Submodule.span C {(1 : C) ⊗ₜ[𝒪] stdBasisVec K 0 +
            ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
              (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K 1}).map (actBaseChange C g₁ (stdFullLattice K)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K)) (stdFullLattice K) := by
  haveI := hdvr
  exact CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent (K := K) π hπ r hres g₁ hg₁ C
    (isNilpotent_of_algHom π n xq) _

omit B in

theorem isUnit_mk_zeta [Fact r.Prime] (n : ℕ) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) (chartVRing.ζ 𝒪 r)) := by
  have h := (chartVRing.isUnit_ζ_pow_sub 𝒪 r).map (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}))
  rw [map_sub, map_pow, show ∀ z : chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)},
      z ^ r - z = z * (z ^ (r - 1) - 1) from fun z => by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (Fact.out : r.Prime).one_lt.le]] at h
  exact isUnit_of_mul_isUnit_left h

end F2Beta3

open F2Beta3 in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (hN : IsSchottky (↥N) (BruhatTits.tree 𝒪 K₀))
    (hNtype : N ≤ typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀))
    (M : MumfordGlueCore 𝒪 π K₀ r g₁ N) :
    ∀ (n : ℕ) (T : Scheme.{0}) (t : Matrix.GeneralLinearGroup (Fin 2) K₀ → (Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) ⟶ T)),
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
      (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq xq' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' P P' : DeligneDatum (K := K₀) π B),
      (d.line (stdFullLattice K₀) =
            Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
      (d'.line (stdFullLattice K₀) =
            Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
      DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P → DeligneDatum.IsPullback (K := K₀) (π := π) B h'⁻¹ d' P' →
      (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') →
      Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ t h = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ t h') →
    ∃! u : M.Z n ⟶ T, ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀, M.ζ h n ≫ u = t h := by
  intro n T t H
  haveI := hdvr
  refine M.desc n T t ?_ ?_ ?_
  ·
    intro g h hg
    obtain ⟨d, hd⟩ := exists_edgeChartDatum (K := K₀) π hdvr hπ hres g₁ hg₁ n
      (AlgHom.id 𝒪 ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
    have key := H _ (g * h) h (AlgHom.id 𝒪 _) (AlgHom.id 𝒪 _) d d (gact π (g * h) d) (gact π h d) hd hd
      (isPullback_gact π (g * h) d) (isPullback_gact π h d)
      ⟨g⁻¹, by rw [map_inv]; exact N.inv_mem hg, by
        rw [show gact π h d = gact π g⁻¹ (gact π (g * h) d) by rw [← gact_mul, inv_mul_cancel_left]]
        exact isPullback_gact π g⁻¹ _⟩
    simpa using key
  ·
    intro h g hg
    obtain ⟨d', hd'⟩ := exists_edgeChartDatum (K := K₀) π hdvr hπ hres g₁ hg₁ n
      (AlgHom.id 𝒪 ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
    obtain ⟨d, hd⟩ := exists_edgeChartDatum (K := K₀) π hdvr hπ hres g₁ hg₁ n (M.α g n).toAlgHom
    have hα : DeligneDatum.IsPullback (K := K₀) (π := π) _ g⁻¹ d' d :=
      M.α_spec g hg n _ (AlgHom.id 𝒪 _) d' d hd' hd
    have hd_eq : d = gact π g d' := eq_gact_of_isPullback π g d' d hα
    have hP : gact π (h * g) d' = gact π 1 (gact π h d) := by rw [gact_one, hd_eq, ← gact_mul]
    have key := H _ h (h * g) (M.α g n).toAlgHom (AlgHom.id 𝒪 _) d d' (gact π h d) (gact π (h * g) d') hd hd'
      (isPullback_gact π h d) (isPullback_gact π (h * g) d')
      ⟨1, by rw [map_one]; exact N.one_mem, by rw [hP]; exact isPullback_gact π 1 _⟩
    have e : Spec.map (CommRingCat.ofHom (AlgHom.id 𝒪 ((chartERing 𝒪 π r) ⧸
        (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))).toRingHom) ≫ t (h * g) = t (h * g) := by simp
    rw [e] at key
    exact key.symm
  ·
    intro h g hg
    obtain ⟨d', hd'1, hd'2, hd'3⟩ := exists_edgeChartDatum (K := K₀) π hdvr hπ hres g₁ hg₁ n (M.ι n)
    obtain ⟨d, hd1, hd2, hd3⟩ := exists_edgeChartDatum (K := K₀) π hdvr hπ hres g₁ hg₁ n ((M.τ g n).toAlgHom.comp (M.ι n))
    have hζu := isUnit_mk_zeta (𝒪 := 𝒪) (r := r) π n

    have h1' : d'.line (stdFullLattice K₀) = Submodule.span _
        {(M.ι n (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : _) ⊗ₜ[𝒪] stdBasisVec K₀ 1} := hd'1
    rw [M.ι_ξ] at h1'
    have h2' := line_edge_to_vertex π g₁ d' _ (M.ι n (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) hζu
      (by rw [mul_comm]; exact M.ι_η n) hd'2

    have hζτu : IsUnit (M.τ g n (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) := hζu.map (M.τ g n)
    have h1 : d.line (stdFullLattice K₀) = Submodule.span _
        {(M.τ g n (M.ι n (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : _) ⊗ₜ[𝒪] stdBasisVec K₀ 1} :=
      hd1
    rw [M.ι_ξ] at h1
    have h2 := line_edge_to_vertex π g₁ d _ (M.τ g n (M.ι n (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)))) hζτu
      (by rw [← map_mul, mul_comm, M.ι_η n, AlgEquiv.commutes]) hd2
    have hτ : DeligneDatum.IsPullback (K := K₀) (π := π) _ g⁻¹ d' d :=
      M.τ_spec g hg n _ (AlgHom.id 𝒪 _) d' d ⟨h1', h2', hd'3⟩ ⟨h1, h2, hd3⟩
    have hd_eq : d = gact π g d' := eq_gact_of_isPullback π g d' d hτ
    have hP : gact π (h * g) d' = gact π 1 (gact π h d) := by rw [gact_one, hd_eq, ← gact_mul]
    have key := H _ h (h * g) ((M.τ g n).toAlgHom.comp (M.ι n)) (M.ι n) d d' (gact π h d) (gact π (h * g) d')
      ⟨hd1, hd2, hd3⟩ ⟨hd'1, hd'2, hd'3⟩ (isPullback_gact π h d) (isPullback_gact π (h * g) d')
      ⟨1, by rw [map_one]; exact N.one_mem, by rw [hP]; exact isPullback_gact π 1 _⟩
    have e : Spec.map (CommRingCat.ofHom ((M.τ g n).toAlgHom.comp (M.ι n)).toRingHom) =
        Spec.map (CommRingCat.ofHom (M.τ g n).toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom (M.ι n).toRingHom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    rw [← key, e, Category.assoc]

end

end S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_univ_law
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_univ_law (solution)
