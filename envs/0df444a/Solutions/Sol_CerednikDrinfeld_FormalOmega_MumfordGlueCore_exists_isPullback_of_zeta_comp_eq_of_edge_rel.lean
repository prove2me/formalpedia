-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_edge_rel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/82826836-65d9-5636-8161-77045fd01117

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_associated_algEquiv_chartERing_xi_eta_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_edge_rel
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_edge_rel.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_edge_rel.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford"

section Kit
namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.DeligneDatum gl_smul_def scalar_eq_scalarGL scalar_smul_vertex tree BruhatTits.gl_smul_def BruhatTits.scalar_eq_scalarGL BruhatTits.tree BruhatTits.scalar_smul_vertex"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "MumfordGlueCore stdFullLattice stdBasisVec DeligneDatum.pullback DeligneDatum.isPullback_pullback Omega Omega.action latticeBaseChange FullLattice.act actBaseChange DeligneDatum DeligneDatum.ext' DeligneDatum.IsPullback chartVRing chartVRing.ζ chartVRing.isUnit_ζ_pow_sub chartERing chartERing.ξ chartERing.η chartERing.corepEquiv chartERing.corepEquiv_apply_val exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent associated_algEquiv_chartERing_xi_eta_of_isPullback"
namespace DeligneDatum
p2m_export "CerednikDrinfeld.FormalOmega.DeligneDatum" "InEdgeChart pullback isPullback_pullback map ext' IsPullback mono invertible line mk"
p2m_open "CerednikDrinfeld.FormalOmega.DeligneDatum CerednikDrinfeld.FormalOmega CerednikDrinfeld"

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem isPullback_iff_eq_pullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g d d' ↔ d' = DeligneDatum.pullback π B g d := by
  constructor
  · intro h
    exact DeligneDatum.ext' (funext h)
  · rintro rfl
    exact DeligneDatum.isPullback_pullback π B g d

namespace IsPullback

private theorem _root_.CerednikDrinfeld.FormalOmega.DeligneDatum.IsPullback.eq {g : Matrix.GeneralLinearGroup (Fin 2) K} {d d' d'' : DeligneDatum (K := K) π B}
    (h' : DeligneDatum.IsPullback (K := K) (π := π) B g d d') (h'' : DeligneDatum.IsPullback (K := K) (π := π) B g d d'') :
    d' = d'' := by
  rw [(isPullback_iff_eq_pullback g d d').mp h', (isPullback_iff_eq_pullback g d d'').mp h'']

end IsPullback
p2m_export "CerednikDrinfeld.FormalOmega.DeligneDatum" "IsPullback.eq"

theorem pullback_one (d : DeligneDatum (K := K) π B) : DeligneDatum.pullback π B 1 d = d := by
  have h := (Omega.action K π).act_one B d
  change DeligneDatum.pullback π B (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ d = d at h
  rwa [inv_one] at h

theorem pullback_mul (a b : Matrix.GeneralLinearGroup (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B (a * b) d = DeligneDatum.pullback π B b (DeligneDatum.pullback π B a d) := by
  have h := (Omega.action K π).act_mul B b⁻¹ a⁻¹ d
  change DeligneDatum.pullback π B (b⁻¹ * a⁻¹)⁻¹ d =
    DeligneDatum.pullback π B b⁻¹⁻¹ (DeligneDatum.pullback π B a⁻¹⁻¹ d) at h
  simp only [mul_inv_rev, inv_inv] at h
  exact h

theorem IsPullback.one (d : DeligneDatum (K := K) π B) : DeligneDatum.IsPullback (K := K) (π := π) B 1 d d := by
  rw [isPullback_iff_eq_pullback, pullback_one]

namespace IsPullback

private theorem _root_.CerednikDrinfeld.FormalOmega.DeligneDatum.IsPullback.trans {a b : Matrix.GeneralLinearGroup (Fin 2) K} {d d' d'' : DeligneDatum (K := K) π B}
    (h₁ : DeligneDatum.IsPullback (K := K) (π := π) B a d d') (h₂ : DeligneDatum.IsPullback (K := K) (π := π) B b d' d'') :
    DeligneDatum.IsPullback (K := K) (π := π) B (a * b) d d'' := by
  rw [isPullback_iff_eq_pullback] at h₁ h₂ ⊢
  rw [h₂, h₁, pullback_mul]

end IsPullback
p2m_export "CerednikDrinfeld.FormalOmega.DeligneDatum" "IsPullback.trans"
namespace IsPullback

private theorem _root_.CerednikDrinfeld.FormalOmega.DeligneDatum.IsPullback.symm {g : Matrix.GeneralLinearGroup (Fin 2) K} {d d' : DeligneDatum (K := K) π B}
    (h : DeligneDatum.IsPullback (K := K) (π := π) B g d d') :
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d' d := by
  rw [isPullback_iff_eq_pullback] at h ⊢
  rw [h, ← pullback_mul, mul_inv_cancel, pullback_one]

end IsPullback
p2m_export "CerednikDrinfeld.FormalOmega.DeligneDatum" "IsPullback.symm"

theorem IsPullback.of_chart_rel {h h' g : Matrix.GeneralLinearGroup (Fin 2) K} {d d' P P' : DeligneDatum (K := K) π B}
    (hd : DeligneDatum.IsPullback (K := K) (π := π) B h⁻¹ d P) (hd' : DeligneDatum.IsPullback (K := K) (π := π) B h'⁻¹ d' P')
    (hg : DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ P P') :
    DeligneDatum.IsPullback (K := K) (π := π) B (h'⁻¹ * g * h)⁻¹ d d' := by
  have := (hd.trans hg).trans hd'.symm
  rw [inv_inv] at this
  rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc]
  exact this

end CerednikDrinfeld.FormalOmega.DeligneDatum
end Kit

noncomputable section

namespace ZetaRelGC6
namespace Coord

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

def coordFun (w : ↥(stdLattice 𝒪 K)) (i : Fin 2) : 𝒪 := Classical.choose (w.2 i)

theorem algebraMap_coordFun (w : ↥(stdLattice 𝒪 K)) (i : Fin 2) :
    algebraMap 𝒪 K (coordFun w i) = (w : Fin 2 → K) i := Classical.choose_spec (w.2 i)

def coordEquiv : ↥(stdLattice 𝒪 K) ≃ₗ[𝒪] (Fin 2 → 𝒪) where
  toFun := coordFun
  map_add' v w := by
    funext i
    apply IsFractionRing.injective 𝒪 K
    rw [algebraMap_coordFun, Pi.add_apply, map_add, algebraMap_coordFun, algebraMap_coordFun]
    rfl
  map_smul' r w := by
    funext i
    apply IsFractionRing.injective 𝒪 K
    rw [algebraMap_coordFun, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, algebraMap_coordFun,
      Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]
  invFun a := ⟨fun i => algebraMap 𝒪 K (a i), fun i => ⟨a i, rfl⟩⟩
  left_inv w := Subtype.ext (funext fun i => algebraMap_coordFun w i)
  right_inv a := funext fun i => IsFractionRing.injective 𝒪 K (by rw [algebraMap_coordFun])

theorem algebraMap_coordEquiv (w : ↥(stdLattice 𝒪 K)) (i : Fin 2) :
    algebraMap 𝒪 K (coordEquiv w i) = (w : Fin 2 → K) i := algebraMap_coordFun w i

theorem coordEquiv_stdBasisVec (j i : Fin 2) :
    coordEquiv (stdBasisVec (𝒪 := 𝒪) K j) i = (Pi.single j 1 : Fin 2 → 𝒪) i := by
  apply IsFractionRing.injective 𝒪 K
  rw [algebraMap_coordEquiv]
  show (Pi.single j (1 : K) : Fin 2 → K) i = algebraMap 𝒪 K ((Pi.single j (1 : 𝒪) : Fin 2 → 𝒪) i)
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

def stdBasis : Module.Basis (Fin 2) 𝒪 ↥(stdFullLattice (𝒪 := 𝒪) K).1 := Module.Basis.ofEquivFun coordEquiv

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def tensorBasis : Module.Basis (Fin 2) B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Algebra.TensorProduct.basis B stdBasis

private def _root_.ZetaRelGC6.Coord.coord (i : Fin 2) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := (tensorBasis B).coord i

p2m_export "ZetaRelGC6.Coord" "coord"
theorem coord_tmul (i : Fin 2) (b : B) (w : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :
    coord B i (b ⊗ₜ[𝒪] w) = b * algebraMap 𝒪 B (coordEquiv w i) := by
  show (Algebra.TensorProduct.basis B stdBasis).repr (b ⊗ₜ[𝒪] w) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [stdBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

theorem coord_tmul_stdBasisVec (i j : Fin 2) (b : B) :
    coord B i (b ⊗ₜ[𝒪] stdBasisVec K j) = if i = j then b else 0 := by
  rw [coord_tmul, coordEquiv_stdBasisVec]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

end ZetaRelGC6.Coord

namespace ZetaRelGC6

abbrev An (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ) : Type :=
  (chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})

variable {r : ℕ} [Fact r.Prime]
  (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
  (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
  (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
  (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

theorem algHom_eq_of_line_eq (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (xq xq' : An 𝒪 π r n →ₐ[𝒪] B) (d : DeligneDatum (K := K₀) π B)
    (hd : (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)))
    (hd' : (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀))) :
    xq = xq' := by
  obtain ⟨h0, h1, -⟩ := hd
  obtain ⟨h0', h1', -⟩ := hd'
  set x := (xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r) with hx
  set x' := (xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r) with hx'
  set y := (xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r) with hy
  set y' := (xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r) with hy'

  have hξ : x' = x := by
    have hmem : x' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1 ∈
        Submodule.span B {x ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1} := by
      rw [← h0, h0']; exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc1 := congrArg (Coord.coord (K := K₀) B 1) hc
    have hc0 := congrArg (Coord.coord (K := K₀) B 0) hc
    simp only [map_smul, map_add, Coord.coord_tmul_stdBasisVec, smul_eq_mul] at hc1 hc0
    simp at hc1 hc0
    rw [hc1, one_mul] at hc0
    exact hc0.symm

  have hη : y' = y := by
    have heq := h1.symm.trans h1'
    have hinj := Submodule.map_injective_of_injective (actBaseChange B g₁ (stdFullLattice K₀)).injective heq
    have hmem : (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + y' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1 ∈
        Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + y ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1} := by
      rw [hinj]; exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 := congrArg (Coord.coord (K := K₀) B 0) hc
    have hc1 := congrArg (Coord.coord (K := K₀) B 1) hc
    simp only [map_smul, map_add, Coord.coord_tmul_stdBasisVec, smul_eq_mul] at hc1 hc0
    simp at hc1 hc0
    rw [hc0, one_mul] at hc1
    exact hc1.symm

  apply Ideal.Quotient.algHom_ext
  apply (chartERing.corepEquiv 𝒪 π r B).injective
  apply Subtype.ext
  rw [chartERing.corepEquiv_apply_val, chartERing.corepEquiv_apply_val]
  exact Prod.ext hξ.symm hη.symm

lemma isNilpotent_of_algHom (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (xq : An 𝒪 π r n →ₐ[𝒪] B) :
    IsNilpotent (algebraMap 𝒪 B π) := by
  refine ⟨n + 1, ?_⟩
  have h1 : (algebraMap 𝒪 (An 𝒪 π r n)) π ^ (n + 1) =
      Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})
        ((algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)) := by
    rw [map_pow]; rfl
  have h2 : (algebraMap 𝒪 (An 𝒪 π r n)) π ^ (n + 1) = 0 := by
    rw [h1]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [← xq.commutes, ← map_pow, h2, map_zero]

abbrev Vn (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ) : Type :=
  chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}

abbrev CHq (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (xq : An 𝒪 π r n →ₐ[𝒪] B) (d : DeligneDatum (K := K₀) π B) : Prop :=
  (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀))

abbrev VCHq (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (y : Vn 𝒪 π r n →ₐ[𝒪] B) (d : DeligneDatum (K := K₀) π B) : Prop :=
  (d.line (stdFullLattice K₀) =
            Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
                (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀))

lemma isUnit_zetaBar (n : ℕ) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) (chartVRing.ζ 𝒪 r)) := by
  have h := (chartVRing.isUnit_ζ_pow_sub 𝒪 r).map (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}))
  have hr : 1 ≤ r := (Fact.out : r.Prime).one_lt.le
  have : chartVRing.ζ 𝒪 r ^ r - chartVRing.ζ 𝒪 r = chartVRing.ζ 𝒪 r * (chartVRing.ζ 𝒪 r ^ (r - 1) - 1) := by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hr]
  rw [this, map_mul] at h
  exact isUnit_of_mul_isUnit_left h

include hdvr hπ hres hg₁ in

lemma exists_CHq (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (xq : An 𝒪 π r n →ₐ[𝒪] B) :
    ∃ d : DeligneDatum (K := K₀) π B, CHq 𝒪 π K₀ g₁ n xq d := by
  haveI := hdvr
  exact exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent (K := K₀) π hπ r hres g₁ hg₁ B
    (isNilpotent_of_algHom 𝒪 π n B xq) (xq.comp (Ideal.Quotient.mkₐ 𝒪 _))

variable (N : Subgroup (PGL(2, K₀))) (M : MumfordGlueCore 𝒪 π K₀ r g₁ N)

theorem VCHq_iff_CHq (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (y : Vn 𝒪 π r n →ₐ[𝒪] B) (d : DeligneDatum (K := K₀) π B) :
    VCHq 𝒪 π K₀ g₁ n y d ↔ CHq 𝒪 π K₀ g₁ n (y.comp (M.ι n)) d := by
  have e1 : ((y.comp (M.ι n)).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
      (chartERing.ξ 𝒪 π r) = y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r)) := by
    show y (M.ι n (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) = _; rw [M.ι_ξ]
  have hu : IsUnit (y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) := (isUnit_zetaBar 𝒪 π n).map y
  have e2 : Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 +
        (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1} =
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 +
        (((y.comp (M.ι n)).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
          (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1} := by
    have hprod : y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r)) * y (M.ι n (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) =
        algebraMap 𝒪 B π := by
      rw [mul_comm, ← map_mul, M.ι_η, AlgHom.commutes]
    have : (y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 +
          (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1 =
        y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r)) • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 +
          (y (M.ι n (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)))) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1) := by
      rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_eq_mul, hprod]
    rw [this, Submodule.span_singleton_smul_eq hu]
    rfl
  unfold VCHq CHq
  rw [e1, e2]

theorem exists_factor_of_isUnit (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (xq : An 𝒪 π r n →ₐ[𝒪] B)
    (hu : IsUnit (xq (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)))) :
    ∃ y : Vn 𝒪 π r n →ₐ[𝒪] B, y.comp (M.ι n) = xq := by
  letI : Algebra (An 𝒪 π r n) (Vn 𝒪 π r n) := (M.ι n).toRingHom.toAlgebra
  haveI : IsLocalization.Away (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r) : An 𝒪 π r n) (Vn 𝒪 π r n) :=
    M.ι_isLocalization n
  have hu' : IsUnit (xq.toRingHom (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) := hu
  let φ : Vn 𝒪 π r n →+* B :=
    IsLocalization.Away.lift (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r) : An 𝒪 π r n) hu'
  have hφ : ∀ a, φ (M.ι n a) = xq a := fun a =>
    IsLocalization.Away.lift_eq (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r) : An 𝒪 π r n) hu' a
  refine ⟨{ toRingHom := φ, commutes' := fun c => ?_ }, ?_⟩
  · show φ (algebraMap 𝒪 (Vn 𝒪 π r n) c) = algebraMap 𝒪 B c
    rw [← (M.ι n).commutes c, hφ, xq.commutes]
  · apply AlgHom.ext
    intro a
    exact hφ a

include hdvr hπ hres hg₁ in

theorem caseV1 (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (h h' g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hgN : Matrix.ProjGenLinGroup.mk g ∈ N)
    (xq xq' : An 𝒪 π r n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B)
    (hd : CHq 𝒪 π K₀ g₁ n xq d) (hd' : CHq 𝒪 π K₀ g₁ n xq' d')
    (hk : DeligneDatum.IsPullback (K := K₀) (π := π) B (h'⁻¹ * g * h)⁻¹ d d')
    (hk0 : Vertex.act (h'⁻¹ * g * h) (stdVertex 𝒪 K₀) = stdVertex 𝒪 K₀)
    (hu : IsUnit (xq (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)))) :
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n := by
  haveI := hdvr
  obtain ⟨y, hy⟩ := exists_factor_of_isUnit 𝒪 π K₀ g₁ N M n xq hu
  subst hy
  have hdV : VCHq 𝒪 π K₀ g₁ n y d := (VCHq_iff_CHq 𝒪 π K₀ g₁ N M n y d).2 hd
  obtain ⟨d₃, hd₃⟩ := exists_CHq 𝒪 hdvr π hπ hres K₀ g₁ hg₁ n ((y.comp (M.τ (h'⁻¹ * g * h) n).toAlgHom).comp (M.ι n))
  have hd₃V : VCHq 𝒪 π K₀ g₁ n (y.comp (M.τ (h'⁻¹ * g * h) n).toAlgHom) d₃ :=
    (VCHq_iff_CHq 𝒪 π K₀ g₁ N M n _ d₃).2 hd₃
  have hk' : DeligneDatum.IsPullback (K := K₀) (π := π) B (h'⁻¹ * g * h)⁻¹ d d₃ :=
    M.τ_spec (h'⁻¹ * g * h) hk0 n B y d d₃ hdV hd₃V
  have hdd : d' = d₃ := hk.eq hk'
  subst hdd
  have hx : xq' = (y.comp (M.τ (h'⁻¹ * g * h) n).toAlgHom).comp (M.ι n) :=
    algHom_eq_of_line_eq 𝒪 π K₀ g₁ n B xq' _ d' hd' hd₃
  have hc1 : CommRingCat.ofHom ((y.comp (M.τ (h'⁻¹ * g * h) n).toAlgHom).comp (M.ι n)).toRingHom =
      CommRingCat.ofHom (M.ι n).toRingHom ≫ CommRingCat.ofHom (M.τ (h'⁻¹ * g * h) n).toAlgHom.toRingHom ≫
        CommRingCat.ofHom y.toRingHom := rfl
  have hc2 : CommRingCat.ofHom (y.comp (M.ι n)).toRingHom =
      CommRingCat.ofHom (M.ι n).toRingHom ≫ CommRingCat.ofHom y.toRingHom := rfl
  have hgh : h' * (h'⁻¹ * g * h) = g * h := by simp only [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hx, hc1, hc2, Spec.map_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, Category.assoc,
    ← M.ζ_vertex h' (h'⁻¹ * g * h) n hk0, hgh, M.ζ_inv g h n hgN]

include hdvr hπ hres hg₁ in

theorem caseA (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (h h' g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hgN : Matrix.ProjGenLinGroup.mk g ∈ N)
    (xq xq' : An 𝒪 π r n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B)
    (hd : (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)))
    (hd' : (d'.line (stdFullLattice K₀) =
          Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)))
    (hk : DeligneDatum.IsPullback (K := K₀) (π := π) B (h'⁻¹ * g * h)⁻¹ d d')
    (hstab : (Vertex.act (h'⁻¹ * g * h) (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧
        Vertex.act (h'⁻¹ * g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
      (Vertex.act (h'⁻¹ * g * h) (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧
        Vertex.act (h'⁻¹ * g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀))) :
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n := by
  haveI := hdvr

  obtain ⟨d'', hd''⟩ := exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent (K := K₀) π hπ r hres g₁ hg₁ B
    (isNilpotent_of_algHom 𝒪 π n B xq) ((xq.comp (M.α (h'⁻¹ * g * h) n).toAlgHom).comp (Ideal.Quotient.mkₐ 𝒪 _))
  have hk' : DeligneDatum.IsPullback (K := K₀) (π := π) B (h'⁻¹ * g * h)⁻¹ d d'' :=
    M.α_spec (h'⁻¹ * g * h) hstab n B xq d d'' hd hd''
  have hdd : d' = d'' := hk.eq hk'
  subst hdd
  have hx : xq' = xq.comp (M.α (h'⁻¹ * g * h) n).toAlgHom :=
    algHom_eq_of_line_eq 𝒪 π K₀ g₁ n B xq' (xq.comp (M.α (h'⁻¹ * g * h) n).toAlgHom) d' hd' hd''
  have hc : CommRingCat.ofHom (xq.comp (M.α (h'⁻¹ * g * h) n).toAlgHom).toRingHom =
      CommRingCat.ofHom (M.α (h'⁻¹ * g * h) n).toAlgHom.toRingHom ≫ CommRingCat.ofHom xq.toRingHom := rfl
  have hgh : h' * (h'⁻¹ * g * h) = g * h := by simp only [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hx, hc, Spec.map_comp, Category.assoc, ← M.ζ_edge h' (h'⁻¹ * g * h) n hstab, hgh, M.ζ_inv g h n hgN]

section Wrev

def swapO : Matrix.GeneralLinearGroup (Fin 2) 𝒪 :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

def swap : Matrix.GeneralLinearGroup (Fin 2) K₀ := Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K₀) (swapO 𝒪)

theorem swap_val : ((swap 𝒪 K₀ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = !![0, 1; 1, 0] := by
  ext i j
  show algebraMap 𝒪 K₀ ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) 𝒪) i j) = _
  fin_cases i <;> fin_cases j <;> simp

theorem act_swap_s₀ : Vertex.act (swap 𝒪 K₀) (stdVertex 𝒪 K₀) = stdVertex 𝒪 K₀ := by
  rw [stdVertex, Vertex.act_mk]
  apply (Vertex.mk_eq_mk_iff).2
  rw [(latticeMap_stdLattice_eq_iff_mem_range (swap 𝒪 K₀)).2 ⟨swapO 𝒪, rfl⟩]
  exact Homothetic.refl _

include hπ in
theorem pi_ne_zero : algebraMap 𝒪 K₀ π ≠ 0 := by
  intro h
  exact hπ.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K₀)).1 h)

def piU : K₀ˣ := Units.mk0 (algebraMap 𝒪 K₀ π) (pi_ne_zero 𝒪 π hπ K₀)

theorem act_scalarGL (c : K₀ˣ) (v : Vertex 𝒪 K₀) : Vertex.act (scalarGL c) v = v := by
  rw [← BruhatTits.gl_smul_def, ← BruhatTits.scalar_eq_scalarGL]
  exact BruhatTits.scalar_smul_vertex c v

def wrev : Matrix.GeneralLinearGroup (Fin 2) K₀ := g₁ * swap 𝒪 K₀

theorem act_wrev_s₀ : Vertex.act (wrev 𝒪 K₀ g₁) (stdVertex 𝒪 K₀) = Vertex.act g₁ (stdVertex 𝒪 K₀) := by
  unfold wrev; rw [Vertex.act_mul, act_swap_s₀]

include hπ hg₁ in
theorem act_wrev_s₁ : Vertex.act (wrev 𝒪 K₀ g₁) (Vertex.act g₁ (stdVertex 𝒪 K₀)) = stdVertex 𝒪 K₀ := by
  unfold wrev
  have key : g₁ * swap 𝒪 K₀ * g₁ = scalarGL (piU 𝒪 π hπ K₀) * swap 𝒪 K₀ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, swap_val, hg₁, scalarGL_coe]
    have : ((piU 𝒪 π hπ K₀ : K₀ˣ) : K₀) = algebraMap 𝒪 K₀ π := rfl
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.smul_apply, this,
        Algebra.algebraMap_eq_smul_one]
  rw [← Vertex.act_mul, key, Vertex.act_mul, act_swap_s₀, act_scalarGL]

include hπ hg₁ in
theorem act_wrev_inv_s₀ : Vertex.act (wrev 𝒪 K₀ g₁)⁻¹ (stdVertex 𝒪 K₀) = Vertex.act g₁ (stdVertex 𝒪 K₀) := by
  conv_lhs => rw [← act_wrev_s₁ 𝒪 π hπ K₀ g₁ hg₁, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

include hπ hg₁ in
theorem Sset_wrev :
    (Vertex.act (wrev 𝒪 K₀ g₁) (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧
        Vertex.act (wrev 𝒪 K₀ g₁) (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
      (Vertex.act (wrev 𝒪 K₀ g₁) (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧
        Vertex.act (wrev 𝒪 K₀ g₁) (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)) :=
  Or.inr ⟨act_wrev_s₀ 𝒪 K₀ g₁, act_wrev_s₁ 𝒪 π hπ K₀ g₁ hg₁⟩

end Wrev

include hdvr hπ hres hg₁ in

theorem reindex (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq : An 𝒪 π r n →ₐ[𝒪] B) (d P : DeligneDatum (K := K₀) π B)
    (hd : CHq 𝒪 π K₀ g₁ n xq d) (hP : DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P) :
    ∃ d₂ : DeligneDatum (K := K₀) π B,
      CHq 𝒪 π K₀ g₁ n (xq.comp (M.α (wrev 𝒪 K₀ g₁) n).toAlgHom) d₂ ∧
      DeligneDatum.IsPullback (K := K₀) (π := π) B (h * (wrev 𝒪 K₀ g₁)⁻¹)⁻¹ d₂ P ∧
      Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n =
        Spec.map (CommRingCat.ofHom (xq.comp (M.α (wrev 𝒪 K₀ g₁) n).toAlgHom).toRingHom) ≫ M.ζ (h * (wrev 𝒪 K₀ g₁)⁻¹) n ∧
      (IsUnit (xq (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) →
        IsUnit ((xq.comp (M.α (wrev 𝒪 K₀ g₁) n).toAlgHom) (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)))) ∧
      (IsUnit (xq (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) →
        IsUnit ((xq.comp (M.α (wrev 𝒪 K₀ g₁) n).toAlgHom) (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)))) := by
  haveI := hdvr
  obtain ⟨d₂, hd₂⟩ := exists_CHq 𝒪 hdvr π hπ hres K₀ g₁ hg₁ n (xq.comp (M.α (wrev 𝒪 K₀ g₁) n).toAlgHom)
  have hw : DeligneDatum.IsPullback (K := K₀) (π := π) B (wrev 𝒪 K₀ g₁)⁻¹ d d₂ :=
    M.α_spec (wrev 𝒪 K₀ g₁) (Sset_wrev 𝒪 π hπ K₀ g₁ hg₁) n B xq d d₂ hd hd₂
  refine ⟨d₂, hd₂, ?_, ?_, ?_, ?_⟩
  · have := hw.symm.trans hP
    rw [inv_inv] at this
    rw [mul_inv_rev, inv_inv]
    exact this
  · have hc : CommRingCat.ofHom (xq.comp (M.α (wrev 𝒪 K₀ g₁) n).toAlgHom).toRingHom =
        CommRingCat.ofHom (M.α (wrev 𝒪 K₀ g₁) n).toAlgHom.toRingHom ≫ CommRingCat.ofHom xq.toRingHom := rfl
    rw [hc, Spec.map_comp, Category.assoc, ← M.ζ_edge (h * (wrev 𝒪 K₀ g₁)⁻¹) (wrev 𝒪 K₀ g₁) n
      (Sset_wrev 𝒪 π hπ K₀ g₁ hg₁), inv_mul_cancel_right]
  · intro hu
    obtain ⟨-, hrev⟩ := associated_algEquiv_chartERing_xi_eta_of_isPullback 𝒪 hdvr π hπ hres K₀ g₁ hg₁ (wrev 𝒪 K₀ g₁) n
      (M.α (wrev 𝒪 K₀ g₁) n) (M.α_spec (wrev 𝒪 K₀ g₁) (Sset_wrev 𝒪 π hπ K₀ g₁ hg₁) n)
    obtain ⟨⟨u, hu1⟩, -⟩ := hrev ⟨act_wrev_s₀ 𝒪 K₀ g₁, act_wrev_s₁ 𝒪 π hπ K₀ g₁ hg₁⟩
    have : xq ((M.α (wrev 𝒪 K₀ g₁) n) (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) * xq u =
        xq (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)) := by rw [← map_mul, hu1]
    show IsUnit (xq ((M.α (wrev 𝒪 K₀ g₁) n) (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))))
    exact isUnit_of_mul_isUnit_left (this ▸ hu)
  · intro hu
    obtain ⟨-, hrev⟩ := associated_algEquiv_chartERing_xi_eta_of_isPullback 𝒪 hdvr π hπ hres K₀ g₁ hg₁ (wrev 𝒪 K₀ g₁) n
      (M.α (wrev 𝒪 K₀ g₁) n) (M.α_spec (wrev 𝒪 K₀ g₁) (Sset_wrev 𝒪 π hπ K₀ g₁ hg₁) n)
    obtain ⟨-, ⟨u, hu1⟩⟩ := hrev ⟨act_wrev_s₀ 𝒪 K₀ g₁, act_wrev_s₁ 𝒪 π hπ K₀ g₁ hg₁⟩
    have : xq ((M.α (wrev 𝒪 K₀ g₁) n) (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) * xq u =
        xq (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) := by rw [← map_mul, hu1]
    show IsUnit (xq ((M.α (wrev 𝒪 K₀ g₁) n) (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))))
    exact isUnit_of_mul_isUnit_left (this ▸ hu)

end ZetaRelGC6

end

open ZetaRelGC6 in
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
    ∀ (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
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
    (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
      ((Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∧ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
        (Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀)))) →
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n →
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' := by
  intro n B _ _ _ h h' xq xq' d d' P P' hd hd' hP hP' hedge heq
  obtain ⟨g, hgN, hrel⟩ := hedge
  haveI := hdvr
  haveI := M.ζ_isOpenImmersion h n
  refine ⟨g, hgN, ?_⟩

  have hc : (Vertex.act ((g * h)⁻¹ * h') (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧
        Vertex.act ((g * h)⁻¹ * h') (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
      (Vertex.act ((g * h)⁻¹ * h') (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧
        Vertex.act ((g * h)⁻¹ * h') (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)) := by
    rcases hrel with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · left
      constructor
      · rw [Vertex.act_mul, h0, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]
      · rw [Vertex.act_mul, h1, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]
    · right
      constructor
      · rw [Vertex.act_mul, h0, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]
      · rw [Vertex.act_mul, h1, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

  have hζ : M.ζ h' n = Spec.map (CommRingCat.ofHom (M.α ((g * h)⁻¹ * h') n).toAlgHom.toRingHom) ≫ M.ζ h n := by
    rw [← M.ζ_inv g h n hgN, ← M.ζ_edge (g * h) ((g * h)⁻¹ * h') n hc, mul_inv_cancel_left]
  have hcomp : CommRingCat.ofHom (xq'.comp (M.α ((g * h)⁻¹ * h') n).toAlgHom).toRingHom =
      CommRingCat.ofHom (M.α ((g * h)⁻¹ * h') n).toAlgHom.toRingHom ≫ CommRingCat.ofHom xq'.toRingHom := rfl
  have hx : xq = xq'.comp (M.α ((g * h)⁻¹ * h') n).toAlgHom := by
    have h1 : Spec.map (CommRingCat.ofHom xq.toRingHom) =
        Spec.map (CommRingCat.ofHom (xq'.comp (M.α ((g * h)⁻¹ * h') n).toAlgHom).toRingHom) := by
      rw [← cancel_mono (M.ζ h n), heq, hζ, hcomp, Spec.map_comp, Category.assoc]
    have h2 := Spec.map_injective h1
    have h3 : xq.toRingHom = (xq'.comp (M.α ((g * h)⁻¹ * h') n).toAlgHom).toRingHom := congrArg CommRingCat.Hom.hom h2
    exact AlgHom.coe_ringHom_injective h3

  have hcd : DeligneDatum.IsPullback (K := K₀) (π := π) B ((g * h)⁻¹ * h')⁻¹ d' d :=
    M.α_spec ((g * h)⁻¹ * h') hc n B xq' d' d hd' (by rw [← hx]; exact hd)
  have := ((hcd.trans hP).symm).trans hP'
  have hgg : ((((g * h)⁻¹ * h')⁻¹ * h⁻¹)⁻¹ * h'⁻¹) = g⁻¹ := by
    group
  rwa [hgg] at this

end S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_edge_rel
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_edge_rel (solution)
