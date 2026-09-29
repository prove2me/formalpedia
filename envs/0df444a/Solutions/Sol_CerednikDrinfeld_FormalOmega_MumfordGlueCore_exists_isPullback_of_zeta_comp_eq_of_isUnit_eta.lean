-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isUnit_eta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/b77062c0-1c20-5cf6-ad2a-131c9edd2fca

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_associated_algEquiv_chartERing_xi_eta_of_isPullback
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isUnit_xi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isUnit_eta
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isUnit_eta.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isUnit_eta.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.MumfordGlueCore FormalOmega.DeligneDatum gl_smul_def scalar_eq_scalarGL scalar_smul_vertex tree BruhatTits.gl_smul_def BruhatTits.scalar_eq_scalarGL BruhatTits.tree BruhatTits.scalar_smul_vertex FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent FormalOmega.associated_algEquiv_chartERing_xi_eta_of_isPullback FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isUnit_xi"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "MumfordGlueCore stdFullLattice stdBasisVec DeligneDatum.pullback DeligneDatum.isPullback_pullback Omega Omega.action FullLattice.act actBaseChange DeligneDatum DeligneDatum.ext' DeligneDatum.IsPullback chartVRing chartVRing.ζ chartVRing.isUnit_ζ_pow_sub chartERing chartERing.ξ chartERing.η exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent associated_algEquiv_chartERing_xi_eta_of_isPullback MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isUnit_xi"
namespace DeligneDatum
p2m_export "CerednikDrinfeld.FormalOmega.DeligneDatum" "InEdgeChart pullback isPullback_pullback map ext' IsPullback line mk"
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
end CerednikDrinfeld.FormalOmega.DeligneDatum

namespace LDV

section Notation
variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ)

abbrev An : Type := (chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})

abbrev Vn : Type := chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}
noncomputable abbrev xiq : An 𝒪 π r n := Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)
noncomputable abbrev etaq : An 𝒪 π r n := Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)
noncomputable abbrev zetaq : Vn 𝒪 π r n := Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r)

end Notation

section Charts
variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) [Fact r.Prime]
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
variable (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)

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

end Charts

section Comb
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
variable (π : 𝒪) (hπ : Irreducible π)
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

theorem act_scalarGL (c : K₀ˣ) (v : Vertex 𝒪 K₀) : Vertex.act (scalarGL c) v = v := by
  rw [← BruhatTits.gl_smul_def, ← BruhatTits.scalar_eq_scalarGL]
  exact BruhatTits.scalar_smul_vertex c v

theorem act_inv_eq_iff (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (v w : Vertex 𝒪 K₀) :
    Vertex.act g⁻¹ v = w ↔ v = Vertex.act g w := by
  constructor
  · intro h; rw [← h, ← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]
  · intro h; rw [h, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

def swapO : Matrix.GeneralLinearGroup (Fin 2) 𝒪 :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

def swap : Matrix.GeneralLinearGroup (Fin 2) K₀ := Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K₀) (swapO 𝒪)

theorem swap_val : ((swap 𝒪 K₀ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = !![0, 1; 1, 0] := by
  ext i j
  show algebraMap 𝒪 K₀ ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) 𝒪) i j) = _
  fin_cases i <;> fin_cases j <;> simp

theorem act_swap_s₀ : Vertex.act (swap 𝒪 K₀) (s₀ 𝒪 K₀) = s₀ 𝒪 K₀ := by
  unfold s₀
  rw [stdVertex, Vertex.act_mk]
  apply (Vertex.mk_eq_mk_iff).2
  rw [(latticeMap_stdLattice_eq_iff_mem_range (swap 𝒪 K₀)).2 ⟨swapO 𝒪, rfl⟩]
  exact Homothetic.refl _

include hπ in
theorem pi_ne_zero : algebraMap 𝒪 K₀ π ≠ 0 := by
  intro h
  exact hπ.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K₀)).1 h)

def piU : K₀ˣ := Units.mk0 (algebraMap 𝒪 K₀ π) (pi_ne_zero 𝒪 π hπ K₀)

def wrev : Matrix.GeneralLinearGroup (Fin 2) K₀ := g₁ * swap 𝒪 K₀

theorem act_wrev_s₀ : Vertex.act (wrev 𝒪 K₀ g₁) (s₀ 𝒪 K₀) = s₁ 𝒪 K₀ g₁ := by
  unfold wrev s₁; rw [Vertex.act_mul, act_swap_s₀]

include hπ hg₁ in
theorem act_wrev_s₁ : Vertex.act (wrev 𝒪 K₀ g₁) (s₁ 𝒪 K₀ g₁) = s₀ 𝒪 K₀ := by
  unfold wrev s₁
  have key : g₁ * swap 𝒪 K₀ * g₁ = scalarGL (piU 𝒪 π hπ K₀) * swap 𝒪 K₀ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, swap_val, hg₁, scalarGL_coe]
    have : ((piU 𝒪 π hπ K₀ : K₀ˣ) : K₀) = algebraMap 𝒪 K₀ π := rfl
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.smul_apply, this,
        Algebra.algebraMap_eq_smul_one]
  show Vertex.act (g₁ * swap 𝒪 K₀) (Vertex.act g₁ (stdVertex 𝒪 K₀)) = stdVertex 𝒪 K₀
  rw [← Vertex.act_mul, key, Vertex.act_mul, act_swap_s₀, act_scalarGL]

include hπ hg₁ in
theorem Sset_wrev : Sset 𝒪 K₀ g₁ (wrev 𝒪 K₀ g₁) :=
  Or.inr ⟨act_wrev_s₀ 𝒪 K₀ g₁, act_wrev_s₁ 𝒪 π hπ K₀ g₁ hg₁⟩

end Comb

section Iota
variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) [Fact r.Prime]
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
variable (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
variable (ι : An 𝒪 π r n →ₐ[𝒪] Vn 𝒪 π r n)
variable (hιξ : ι (xiq 𝒪 π r n) = zetaq 𝒪 π r n)
variable (hιη : ι (etaq 𝒪 π r n) * zetaq 𝒪 π r n = algebraMap 𝒪 (Vn 𝒪 π r n) π)
variable (hloc : @IsLocalization.Away (An 𝒪 π r n) _ (xiq 𝒪 π r n) (Vn 𝒪 π r n) _ ι.toRingHom.toAlgebra)

theorem isUnit_zetaq : IsUnit (zetaq 𝒪 π r n) := by
  have h := (chartVRing.isUnit_ζ_pow_sub 𝒪 r).map (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}))
  have hr : 1 ≤ r := (Fact.out : r.Prime).one_lt.le
  have : chartVRing.ζ 𝒪 r ^ r - chartVRing.ζ 𝒪 r = chartVRing.ζ 𝒪 r * (chartVRing.ζ 𝒪 r ^ (r - 1) - 1) := by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hr]
  rw [this, map_mul] at h
  exact isUnit_of_mul_isUnit_left h

include hιξ hιη in

theorem VCH_iff_CH {B : Type} [CommRing B] [Algebra 𝒪 B] (y : Vn 𝒪 π r n →ₐ[𝒪] B) (d : DeligneDatum (K := K₀) π B) :
    VCH 𝒪 π r K₀ g₁ n y d ↔ CH 𝒪 π r K₀ g₁ n (y.comp ι) d := by
  have e1 : ((y.comp ι).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
      (chartERing.ξ 𝒪 π r) = y (zetaq 𝒪 π r n) := by
    show y (ι (xiq 𝒪 π r n)) = _; rw [hιξ]
  have hu : IsUnit (y (zetaq 𝒪 π r n)) := (isUnit_zetaq 𝒪 π r n).map y
  have e2 : Submodule.span B {(y (zetaq 𝒪 π r n)) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1} =
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 +
        (((y.comp ι).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
          (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1} := by
    have hprod : y (zetaq 𝒪 π r n) * y (ι (etaq 𝒪 π r n)) = algebraMap 𝒪 B π := by
      rw [mul_comm, ← map_mul, hιη, AlgHom.commutes]
    have : (y (zetaq 𝒪 π r n)) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1 =
        y (zetaq 𝒪 π r n) • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (y (ι (etaq 𝒪 π r n))) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1) := by
      rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_eq_mul, hprod]
    rw [this, Submodule.span_singleton_smul_eq hu]
    rfl
  unfold VCH CH
  rw [e1, e2]

include hloc in

theorem exists_lift {B : Type} [CommRing B] [Algebra 𝒪 B] (xq : An 𝒪 π r n →ₐ[𝒪] B) (hu : IsUnit (xq (xiq 𝒪 π r n))) :
    ∃ y : Vn 𝒪 π r n →ₐ[𝒪] B, y.comp ι = xq := by
  letI : Algebra (An 𝒪 π r n) (Vn 𝒪 π r n) := ι.toRingHom.toAlgebra
  haveI := hloc
  have hu' : IsUnit (xq.toRingHom (xiq 𝒪 π r n)) := hu
  let f : Vn 𝒪 π r n →+* B := IsLocalization.Away.lift (xiq 𝒪 π r n) hu'
  have hf : f.comp (algebraMap (An 𝒪 π r n) (Vn 𝒪 π r n)) = xq.toRingHom := IsLocalization.Away.lift_comp (xiq 𝒪 π r n) hu'
  have hfι : ∀ a, f (ι a) = xq a := fun a => by
    have := congrArg (fun φ : An 𝒪 π r n →+* B => φ a) hf
    exact this
  refine ⟨{ toRingHom := f, commutes' := ?_ }, ?_⟩
  · intro o
    show f (algebraMap 𝒪 (Vn 𝒪 π r n) o) = algebraMap 𝒪 B o
    rw [← ι.commutes o, hfι, xq.commutes]
  · apply AlgHom.ext
    intro a
    exact hfι a

end Iota

section Main

theorem exists_CH {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (xq : An 𝒪 π r n →ₐ[𝒪] B) :
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

theorem algHom_eq_of_comp_zeta_eq {r : ℕ}
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀))) (M : MumfordGlueCore 𝒪 π K₀ r g₁ N)
    (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (h : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (x x' : An 𝒪 π r n →ₐ[𝒪] B)
    (e : Spec.map (CommRingCat.ofHom x.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom x'.toRingHom) ≫ M.ζ h n) :
    x = x' := by
  haveI := M.ζ_isOpenImmersion h n
  have e1 := (cancel_mono (M.ζ h n)).mp e
  have e2 : CommRingCat.ofHom x.toRingHom = CommRingCat.ofHom x'.toRingHom := Spec.map_injective e1
  have e3 : x.toRingHom = x'.toRingHom := congrArg CommRingCat.Hom.hom e2
  exact AlgHom.ext fun a => congrArg (fun φ : An 𝒪 π r n →+* B => φ a) e3

end Main

end LDV

open LDV in
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
    IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) →
    (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
      (Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))) →
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n →
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' := by
  intro n B _ _ _ h h' xq xq' d d' P P' hd hd' hP hP' hu hC2 hζ
  haveI := hdvr

  obtain ⟨w, hw⟩ : ∃ w : Matrix.GeneralLinearGroup (Fin 2) K₀, w = wrev 𝒪 K₀ g₁ := ⟨_, rfl⟩
  have hw0 : Vertex.act w (stdVertex 𝒪 K₀) = Vertex.act g₁ (stdVertex 𝒪 K₀) := by rw [hw]; exact act_wrev_s₀ 𝒪 K₀ g₁
  have hw1 : Vertex.act w (Vertex.act g₁ (stdVertex 𝒪 K₀)) = stdVertex 𝒪 K₀ := by rw [hw]; exact act_wrev_s₁ 𝒪 π hπ K₀ g₁ hg₁
  have hSw : Sset 𝒪 K₀ g₁ w := Or.inr ⟨hw0, hw1⟩
  obtain ⟨xq₂, hxq₂⟩ : ∃ xq₂ : An 𝒪 π r n →ₐ[𝒪] B, xq₂ = xq'.comp (M.α w n).symm.toAlgHom := ⟨_, rfl⟩
  have hx : xq₂.comp (M.α w n).toAlgHom = xq' := by
    rw [hxq₂]
    apply AlgHom.ext
    intro a
    show xq' ((M.α w n).symm ((M.α w n) a)) = xq' a
    rw [AlgEquiv.symm_apply_apply]

  obtain ⟨d₂, hd₂⟩ := exists_CH 𝒪 hdvr π hπ hres K₀ g₁ hg₁ n xq₂
  have hwd : DeligneDatum.IsPullback (K := K₀) (π := π) B w⁻¹ d₂ d' :=
    M.α_spec w hSw n B xq₂ d₂ d' hd₂ (by rw [hx]; exact hd')
  have hP₂ : DeligneDatum.IsPullback (K := K₀) (π := π) B (h' * w)⁻¹ d₂ P' := by
    rw [mul_inv_rev]; exact hwd.trans hP'

  have hζ₂ : Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n =
      Spec.map (CommRingCat.ofHom xq₂.toRingHom) ≫ M.ζ (h' * w) n := by
    rw [hζ, M.ζ_edge h' w n hSw, ← hx]
    have c : CommRingCat.ofHom (xq₂.comp (M.α w n).toAlgHom).toRingHom =
        CommRingCat.ofHom (M.α w n).toAlgHom.toRingHom ≫ CommRingCat.ofHom xq₂.toRingHom := rfl
    rw [c, Spec.map_comp, Category.assoc]

  have hends := CerednikDrinfeld.FormalOmega.associated_algEquiv_chartERing_xi_eta_of_isPullback
    𝒪 hdvr π hπ hres K₀ g₁ hg₁ w n (M.α w n) (M.α_spec w hSw n)
  obtain ⟨-, hαη⟩ := hends.2 ⟨hw0, hw1⟩
  have hu₂ : IsUnit (xq₂ (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) := by
    obtain ⟨u, hu'⟩ := hαη
    rw [← hu', map_mul]
    refine IsUnit.mul ?_ (u.isUnit.map xq₂)
    have e : xq₂ ((M.α w n) (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) = xq' (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)) := by
      rw [hxq₂]
      show xq' ((M.α w n).symm ((M.α w n) _)) = _
      rw [AlgEquiv.symm_apply_apply]
    rw [e]; exact hu

  have hC1 : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
      (Vertex.act (h' * w) (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨
        Vertex.act (h' * w) (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀))) := by
    obtain ⟨g, hgN, hor⟩ := hC2
    refine ⟨g, hgN, ?_⟩
    rw [Vertex.act_mul, hw0]
    exact hor
  exact CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isUnit_xi 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N hN hNtype M
    n B h (h' * w) xq xq₂ d d₂ P P' hd hd₂ hP hP₂ hu₂ hC1 hζ₂

end S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isUnit_eta
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isUnit_eta (solution)
