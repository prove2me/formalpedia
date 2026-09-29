-- Prove2me | solution 1 for CuspidalType.IsCuspidalOfType.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ba3d69af-28ae-5847-9f6c-899441001394

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_IsCuspidalOfType_baseChange

set_option autoImplicit false

open scoped TensorProduct

open CuspidalType
open scoped CuspidalType

private theorem charpoly_ind_map {q : ℕ} [Fact q.Prime] (K : Type*) [Field K] (K' : Type*) [Field K'] [Algebra K K']
    (g : GL2 q) : (ind q K' g).charpoly = (ind q K g).charpoly.map (algebraMap K K') := by
  classical
  haveI : Fintype (ProjLine q) := Fintype.ofFinite _
  rw [← LinearMap.charpoly_toMatrix (ind q K' g) Finsupp.basisSingleOne,
    ← LinearMap.charpoly_toMatrix (ind q K g) Finsupp.basisSingleOne, ← Matrix.charpoly_map]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, Representation.ofMulActionFinsupp_single, Finsupp.single_apply]

private theorem eq_zero_of_forall_baseChange_eq_zero {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] (f : ι → Module.End K V) (hf : ∀ v : V, (∀ t, f t v = 0) → v = 0) (K' : Type*) [Field K']
    [Algebra K K'] (x : K' ⊗[K] V) (hx : ∀ t, (f t).baseChange K' x = 0) : x = 0 := by
  classical
  let Φ : V →ₗ[K] (ι → V) := LinearMap.pi f
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hf v fun t => by simpa [Φ] using congrFun hv t
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective Φ hΦ
  have hid : ∀ v : V, ∑ t, ψ (LinearMap.single K (fun _ : ι => V) t (f t v)) = v := by
    intro v
    rw [← map_sum]
    have h1 : (∑ t, LinearMap.single K (fun _ : ι => V) t (f t v)) = Φ v := by
      ext s
      simp [Φ, Finset.sum_apply, Pi.single_apply]
    rw [h1]
    exact LinearMap.congr_fun hψ v
  have hall : ∀ y : K' ⊗[K] V,
      ∑ t, (ψ ∘ₗ LinearMap.single K (fun _ : ι => V) t).baseChange K' ((f t).baseChange K' y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      simp only [LinearMap.baseChange_tmul, LinearMap.comp_apply, ← TensorProduct.tmul_sum, hid]
    | add y z hy hz =>
      simp only [map_add, Finset.sum_add_distrib, hy, hz]
  rw [← hall x]
  simp [hx]

open CuspidalType in
theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {σ : Representation K (GL2 q) V} (h : IsCuspidalOfType θ σ)
    (K' : Type*) [Field K'] [Algebra K K'] :
    IsCuspidalOfType ((Units.map (algebraMap K K').toMonoidHom).comp θ)
      ((Module.End.baseChangeHom K K' V : Module.End K V →* Module.End K' (K' ⊗[K] V)).comp σ) := by
  have hρ' : ∀ g : GL2 q,
      ((Module.End.baseChangeHom K K' V : Module.End K V →* Module.End K' (K' ⊗[K] V)).comp σ) g =
        (σ g).baseChange K' := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Module.finrank_baseChange, h.finrank_eq]
  · intro v hv
    refine eq_zero_of_forall_baseChange_eq_zero (fun t : ZMod q => σ (unipotent q t) - LinearMap.id) ?_ K' v ?_
    · intro w hw
      refine h.cuspidal w fun t => ?_
      have hwt := hw t
      rwa [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hwt
    · intro t
      rw [LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact hv t
  · intro c
    rw [hρ', h.central c, LinearMap.baseChange_id]
  · intro α
    rw [hρ', LinearMap.charpoly_baseChange, charpoly_ind_map K K', ← h.torus_charpoly α, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_C]
    simp [Units.coe_map, MonoidHom.coe_coe]

end S_CuspidalType_IsCuspidalOfType_baseChange
end P2MW
export P2MW.S_CuspidalType_IsCuspidalOfType_baseChange (solution)
