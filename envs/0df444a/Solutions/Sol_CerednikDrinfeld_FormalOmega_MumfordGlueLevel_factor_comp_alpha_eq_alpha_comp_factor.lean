-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlueLevel.factor_comp_alpha_eq_alpha_comp_factor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/449d82f7-b01b-53d7-9e4b-9593e4881c65

import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_alpha_eq_alpha_comp_factor
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace MGL

section Notation
variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ)

abbrev An : Type := (chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})

abbrev Vn : Type := chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}

abbrev xiq : An 𝒪 π r n := Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)
abbrev etaq : An 𝒪 π r n := Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)
abbrev zetaq : Vn 𝒪 π r n := Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r)

end Notation

section Translate
variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

abbrev tr (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : DeligneDatum (K := K₀) π B) : DeligneDatum (K := K₀) π B :=
  (Omega.action K₀ π).act B g d

theorem tr_one (d : DeligneDatum (K := K₀) π B) : tr π 1 d = d := (Omega.action K₀ π).act_one B d

theorem tr_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : DeligneDatum (K := K₀) π B) :
    tr π (g * h) d = tr π g (tr π h d) := (Omega.action K₀ π).act_mul B g h d

theorem isPullback_inv_iff (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (d d' : DeligneDatum (K := K₀) π B) :
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d' ↔ d' = tr π g d := by
  constructor
  · intro h
    apply DeligneDatum.ext'
    funext M
    exact h M
  · rintro rfl
    exact DeligneDatum.isPullback_pullback π B g⁻¹ d

theorem isPullback_inv_tr (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : DeligneDatum (K := K₀) π B) :
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d (tr π g d) :=
  (isPullback_inv_iff π g d _).2 rfl

end Translate

end MGL

namespace MGL

section Transport
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
variable (π : 𝒪) (hπ : Irreducible π) (r : ℕ) [Fact r.Prime] (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

abbrev s₀ : Vertex 𝒪 K₀ := stdVertex 𝒪 K₀
abbrev s₁ : Vertex 𝒪 K₀ := Vertex.act g₁ (stdVertex 𝒪 K₀)

abbrev Sset (g : Matrix.GeneralLinearGroup (Fin 2) K₀) : Prop :=
  (Vertex.act g (s₀ 𝒪 K₀) = s₀ 𝒪 K₀ ∧ Vertex.act g (s₁ 𝒪 K₀ g₁) = s₁ 𝒪 K₀ g₁) ∨
  (Vertex.act g (s₀ 𝒪 K₀) = s₁ 𝒪 K₀ g₁ ∧ Vertex.act g (s₁ 𝒪 K₀ g₁) = s₀ 𝒪 K₀)

abbrev CH (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (xq : An 𝒪 π r n →ₐ[𝒪] B) (d : DeligneDatum (K := K₀) π B) : Prop :=
  d.line (stdFullLattice K₀) =
      Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
    d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
        (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
    d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)

abbrev VCH (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (y : Vn 𝒪 π r n →ₐ[𝒪] B) (d : DeligneDatum (K := K₀) π B) : Prop :=
  d.line (stdFullLattice K₀) =
      Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
    d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
      (Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
          (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
    d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)

abbrev EdgeTP (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (α : An 𝒪 π r n ≃ₐ[𝒪] An 𝒪 π r n) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (xq : An 𝒪 π r n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B),
    CH 𝒪 π r K₀ g₁ n xq d → CH 𝒪 π r K₀ g₁ n (xq.comp α.toAlgHom) d' → DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d'

abbrev VertTP (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (τ : Vn 𝒪 π r n ≃ₐ[𝒪] Vn 𝒪 π r n) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (y : Vn 𝒪 π r n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B),
    VCH 𝒪 π r K₀ g₁ n y d → VCH 𝒪 π r K₀ g₁ n (y.comp τ.toAlgHom) d' → DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d'

include hdvr hπ hres hg₁ in

theorem exists_CH (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (xq : An 𝒪 π r n →ₐ[𝒪] B) :
    ∃ d : DeligneDatum (K := K₀) π B, CH 𝒪 π r K₀ g₁ n xq d := by
  haveI := hdvr
  have hB : IsNilpotent (algebraMap 𝒪 B π) := by
    refine ⟨n + 1, ?_⟩
    have h1 : (xq.comp (Ideal.Quotient.mkₐ 𝒪 _)) ((algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)) = 0 := by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      have h0 : (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r)) π ^ (n + 1)}))
          ((algebraMap 𝒪 (chartERing 𝒪 π r)) π ^ (n + 1)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      rw [h0, map_zero]
    rw [map_pow, AlgHom.commutes] at h1
    exact h1
  exact CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent π hπ r hres g₁ hg₁ B hB
    (xq.comp (Ideal.Quotient.mkₐ 𝒪 _))

end Transport
end MGL

namespace MGL
section Transport2
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
variable (π : 𝒪) (hπ : Irreducible π) (r : ℕ) [Fact r.Prime] (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

include hdvr hπ in
theorem CH_unique (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] {xq : An 𝒪 π r n →ₐ[𝒪] B}
    {d d' : DeligneDatum (K := K₀) π B} (h : CH 𝒪 π r K₀ g₁ n xq d) (h' : CH 𝒪 π r K₀ g₁ n xq d') : d' = d := by
  haveI := hdvr
  exact DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ d d' _ _ h.2.2 (h'.1.trans h.1.symm) (h'.2.1.trans h.2.1.symm)

include hdvr hπ in
theorem VCH_unique (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] {y : Vn 𝒪 π r n →ₐ[𝒪] B}
    {d d' : DeligneDatum (K := K₀) π B} (h : VCH 𝒪 π r K₀ g₁ n y d) (h' : VCH 𝒪 π r K₀ g₁ n y d') : d' = d := by
  haveI := hdvr
  exact DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ d d' _ _ h.2.2 (h'.1.trans h.1.symm) (h'.2.1.trans h.2.1.symm)

end Transport2
end MGL

namespace MGL
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

theorem coordEquiv_eq_of {w : ↥(stdLattice 𝒪 K)} {i : Fin 2} {r : 𝒪} (h : (w : Fin 2 → K) i = algebraMap 𝒪 K r) :
    coordEquiv w i = r :=
  IsFractionRing.injective 𝒪 K (by rw [algebraMap_coordEquiv, h])

theorem coordEquiv_stdBasisVec (j i : Fin 2) :
    coordEquiv (stdBasisVec (𝒪 := 𝒪) K j) i = (Pi.single j 1 : Fin 2 → 𝒪) i := by
  apply coordEquiv_eq_of
  show (Pi.single j (1 : K) : Fin 2 → K) i = algebraMap 𝒪 K ((Pi.single j (1 : 𝒪) : Fin 2 → 𝒪) i)
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

def stdBasis : Module.Basis (Fin 2) 𝒪 ↥(stdFullLattice (𝒪 := 𝒪) K).1 := Module.Basis.ofEquivFun coordEquiv

theorem stdBasis_repr (w : ↥(stdFullLattice (𝒪 := 𝒪) K).1) (i : Fin 2) : stdBasis.repr w i = coordEquiv w i := by
  show (Module.Basis.ofEquivFun coordEquiv).repr w i = _
  rw [Module.Basis.ofEquivFun_repr_apply]

theorem stdBasis_apply (i : Fin 2) : stdBasis i = stdBasisVec (𝒪 := 𝒪) K i := by
  apply stdBasis.repr.injective
  ext j
  rw [Module.Basis.repr_self, stdBasis_repr, coordEquiv_stdBasisVec, Finsupp.single_apply, Pi.single_apply]
  simp only [eq_comm]

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def tensorBasis : Module.Basis (Fin 2) B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Algebra.TensorProduct.basis B stdBasis

theorem tensorBasis_apply (i : Fin 2) : tensorBasis B i = (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K i := by
  rw [tensorBasis, Algebra.TensorProduct.basis_apply, stdBasis_apply]

private def _root_.MGL.Coord.coord (i : Fin 2) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := (tensorBasis B).coord i

p2m_export "MGL.Coord" "coord"
theorem coord_tmul (i : Fin 2) (b : B) (w : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :
    coord B i (b ⊗ₜ[𝒪] w) = b * algebraMap 𝒪 B (coordEquiv w i) := by
  show (Algebra.TensorProduct.basis B stdBasis).repr (b ⊗ₜ[𝒪] w) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [stdBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

theorem coord_tmul_stdBasisVec (i j : Fin 2) (b : B) :
    coord B i (b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K j) = if i = j then b else 0 := by
  rw [coord_tmul, coordEquiv_stdBasisVec]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

omit B in
theorem coordEquiv_smul_stdBasisVec (r : 𝒪) (j i : Fin 2) :
    coordEquiv (r • stdBasisVec (𝒪 := 𝒪) K j) i = r * (Pi.single j 1 : Fin 2 → 𝒪) i := by
  apply coordEquiv_eq_of
  show r • ((Pi.single j (1 : K) : Fin 2 → K) i) = algebraMap 𝒪 K (r * (Pi.single j (1 : 𝒪) : Fin 2 → 𝒪) i)
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same, mul_one, Algebra.smul_def, mul_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, smul_zero, mul_zero, map_zero]

theorem coord_tmul_smul_stdBasisVec (i j : Fin 2) (b : B) (r : 𝒪) :
    coord B i (b ⊗ₜ[𝒪] (r • stdBasisVec (𝒪 := 𝒪) K j)) = if i = j then b * algebraMap 𝒪 B r else 0 := by
  rw [coord_tmul, coordEquiv_smul_stdBasisVec]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

theorem eq_sum_coord (x : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :
    x = coord B 0 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0) + coord B 1 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1) := by
  have h := (tensorBasis B).sum_repr x
  rw [Fin.sum_univ_two, tensorBasis_apply, tensorBasis_apply] at h
  exact h.symm

variable {B}

def D0 (ξ : B) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := coord B 0 - ξ • coord B 1

def D1 (η : B) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := coord B 1 - η • coord B 0

theorem D0_apply (ξ : B) (x : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :
    D0 ξ x = coord B 0 x - ξ * coord B 1 x := rfl

theorem D1_apply (η : B) (x : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :
    D1 η x = coord B 1 x - η * coord B 0 x := rfl

abbrev N0 (ξ : B) : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Submodule.span B {ξ ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}

abbrev N1' (η : B) : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + η ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}

theorem N0_eq_ker (ξ : B) : N0 (𝒪 := 𝒪) (K := K) ξ = LinearMap.ker (D0 (𝒪 := 𝒪) (K := K) ξ) := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, D0_apply]
    simp [map_add, coord_tmul_stdBasisVec]
  · intro x hx
    rw [LinearMap.mem_ker, D0_apply, sub_eq_zero] at hx
    rw [eq_sum_coord B x, hx]
    have : (ξ * coord B 1 x) • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0) + coord B 1 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1)
        = coord B 1 x • (ξ ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1) := by
      simp only [smul_add, TensorProduct.smul_tmul', smul_eq_mul, mul_one, mul_comm ξ]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem N1'_eq_ker (η : B) : N1' (𝒪 := 𝒪) (K := K) η = LinearMap.ker (D1 (𝒪 := 𝒪) (K := K) η) := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, D1_apply]
    simp [map_add, coord_tmul_stdBasisVec]
  · intro x hx
    rw [LinearMap.mem_ker, D1_apply, sub_eq_zero] at hx
    rw [eq_sum_coord B x, hx]
    have : coord B 0 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0) + (η * coord B 0 x) • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1)
        = coord B 0 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + η ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1) := by
      simp only [smul_add, TensorProduct.smul_tmul', smul_eq_mul, mul_one, mul_comm η]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Coord
end MGL

namespace MGL
section IotaTau
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
variable (π : 𝒪) (hπ : Irreducible π) (r : ℕ) [Fact r.Prime] (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

theorem algHom_An_ext (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] {x x' : An 𝒪 π r n →ₐ[𝒪] B}
    (hξ : x (xiq 𝒪 π r n) = x' (xiq 𝒪 π r n)) (hη : x (etaq 𝒪 π r n) = x' (etaq 𝒪 π r n)) : x = x' := by
  apply Ideal.Quotient.algHom_ext
  apply (chartERing.corepEquiv 𝒪 π r B).injective
  apply Subtype.ext
  rw [chartERing.corepEquiv_apply_val, chartERing.corepEquiv_apply_val]
  exact Prod.ext hξ hη

theorem algHom_Vn_ext (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] {y y' : Vn 𝒪 π r n →ₐ[𝒪] B}
    (hζ : y (zetaq 𝒪 π r n) = y' (zetaq 𝒪 π r n)) : y = y' := by
  apply Ideal.Quotient.algHom_ext
  apply (chartVRing.corepEquiv 𝒪 r B).injective
  apply Subtype.ext
  rw [chartVRing.corepEquiv_apply_val, chartVRing.corepEquiv_apply_val]
  exact hζ

theorem fst_eq_of_span_eq {B : Type} [CommRing B] [Algebra 𝒪 B] {a a' : B}
    (h : Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1} =
      Submodule.span B {a' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1}) : a = a' := by
  have hm : a' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1 ∈ Coord.N0 (𝒪 := 𝒪) (K := K₀) a := by
    show _ ∈ Submodule.span B _
    rw [h]; exact Submodule.mem_span_singleton_self _
  rw [Coord.N0_eq_ker, LinearMap.mem_ker, Coord.D0_apply] at hm
  simp only [map_add, Coord.coord_tmul_stdBasisVec] at hm
  simpa [sub_eq_zero, eq_comm] using hm

theorem snd_eq_of_span_map_eq {B : Type} [CommRing B] [Algebra 𝒪 B] {b b' : B}
    (h : (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1}).map
        (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1}).map
        (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap) : b = b' := by
  have h' := Submodule.map_injective_of_injective (actBaseChange B g₁ (stdFullLattice K₀)).injective h
  have hm : (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1 ∈ Coord.N1' (𝒪 := 𝒪) (K := K₀) b := by
    show _ ∈ Submodule.span B _
    rw [h']; exact Submodule.mem_span_singleton_self _
  rw [Coord.N1'_eq_ker, LinearMap.mem_ker, Coord.D1_apply] at hm
  simp only [map_add, Coord.coord_tmul_stdBasisVec] at hm
  simpa [sub_eq_zero, eq_comm] using hm

theorem eq_of_CH_CH (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] {x x' : An 𝒪 π r n →ₐ[𝒪] B}
    {d : DeligneDatum (K := K₀) π B} (h : CH 𝒪 π r K₀ g₁ n x d) (h' : CH 𝒪 π r K₀ g₁ n x' d) : x = x' := by
  apply algHom_An_ext
  · exact fst_eq_of_span_eq 𝒪 K₀ (h.1.symm.trans h'.1)
  · exact snd_eq_of_span_map_eq 𝒪 K₀ g₁ (h.2.1.symm.trans h'.2.1)

theorem eq_of_VCH_VCH (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] {y y' : Vn 𝒪 π r n →ₐ[𝒪] B}
    {d : DeligneDatum (K := K₀) π B} (h : VCH 𝒪 π r K₀ g₁ n y d) (h' : VCH 𝒪 π r K₀ g₁ n y' d) : y = y' :=
  algHom_Vn_ext 𝒪 π r n (fst_eq_of_span_eq 𝒪 K₀ (h.1.symm.trans h'.1))

theorem isUnit_zetaq (n : ℕ) : IsUnit (zetaq 𝒪 π r n) := by
  have h := (chartVRing.isUnit_ζ_pow_sub 𝒪 r).map (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}))
  have hr : 1 ≤ r := (Fact.out : r.Prime).one_lt.le
  have : chartVRing.ζ 𝒪 r ^ r - chartVRing.ζ 𝒪 r = chartVRing.ζ 𝒪 r * (chartVRing.ζ 𝒪 r ^ (r - 1) - 1) := by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hr]
  rw [this, map_mul] at h
  exact isUnit_of_mul_isUnit_left h

end IotaTau
end MGL

end

open MGL in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀))) (n : ℕ)
    (L : MumfordGlueLevel 𝒪 π K₀ r g₁ N n) (L' : MumfordGlueLevel 𝒪 π K₀ r g₁ N (n + 1))
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hg : (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
      (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀))) :
    (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1))))).comp (L'.α g).toAlgHom.toRingHom =
      (L.α g).toAlgHom.toRingHom.comp (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1))))) := by
  haveI := hdvr
  let fA : An 𝒪 π r (n + 1) →ₐ[𝒪] An 𝒪 π r n := Ideal.Quotient.factorₐ 𝒪
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1))))

  obtain ⟨d₀, hd₀⟩ := exists_CH 𝒪 hdvr π hπ r hres K₀ g₁ hg₁ n (AlgHom.id 𝒪 (An 𝒪 π r n))
  obtain ⟨d₁, hd₁⟩ := exists_CH 𝒪 hdvr π hπ r hres K₀ g₁ hg₁ n (L.α g).toAlgHom
  obtain ⟨d₂, hd₂⟩ := exists_CH 𝒪 hdvr π hπ r hres K₀ g₁ hg₁ (n + 1) (fA.comp (L'.α g).toAlgHom)

  have hP1 : DeligneDatum.IsPullback (K := K₀) (π := π) (An 𝒪 π r n) g⁻¹ d₀ d₁ :=
    L.α_spec g hg (An 𝒪 π r n) (AlgHom.id 𝒪 (An 𝒪 π r n)) d₀ d₁ hd₀ hd₁

  have hd₀' : CH 𝒪 π r K₀ g₁ (n + 1) fA d₀ := hd₀
  have hP2 : DeligneDatum.IsPullback (K := K₀) (π := π) (An 𝒪 π r n) g⁻¹ d₀ d₂ :=
    L'.α_spec g hg (An 𝒪 π r n) fA d₀ d₂ hd₀' hd₂
  have e1 := (isPullback_inv_iff π g d₀ d₁).1 hP1
  have e2 := (isPullback_inv_iff π g d₀ d₂).1 hP2
  have hd₁' : CH 𝒪 π r K₀ g₁ (n + 1) ((L.α g).toAlgHom.comp fA) d₂ := by
    rw [e2, ← e1]; exact hd₁
  have key : fA.comp (L'.α g).toAlgHom = (L.α g).toAlgHom.comp fA := eq_of_CH_CH 𝒪 π r K₀ g₁ (n + 1) hd₂ hd₁'
  exact RingHom.ext fun a => AlgHom.congr_fun key a

end S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_alpha_eq_alpha_comp_factor
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_alpha_eq_alpha_comp_factor (solution)
