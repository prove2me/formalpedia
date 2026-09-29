-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.mem_of_eq_algebraMap_of_eq_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fa782219-056b-58b0-a493-0f910959e244

import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_BaseChange
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_mem_of_eq_algebraMap_of_eq_mul_conj

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open scoped Classical

noncomputable section

namespace Scalar21

variable {a b : ℚ}
open CerednikDrinfeld.CosetGraph

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

def localUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup (Loc a b w)ˣ where
  carrier := Submodule.localBoxUnits Λ w
  one_mem' := by
    have h1 : ((1 : (Loc a b w)ˣ) : Loc a b w) ∈ (Submodule.localBox Λ w : Set (Loc a b w)) := by
      rw [Units.val_one]
      exact AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩
    exact ⟨h1, by rw [inv_one]; exact h1⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact localBox_mul_mem hΛ w hx.1 hy.1
    · rw [mul_inv_rev, Units.val_mul]; exact localBox_mul_mem hΛ w hy.2 hx.2
  inv_mem' := by
    intro x hx
    exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem mem_awayUnits_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (v : HeightOneSpectrum (𝓞 ℚ))
    (γ : (ℍ[ℚ, a, b])ˣ) :
    γ ∈ awayUnits R v ↔ ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → toLoc w γ ∈ Submodule.localBoxUnits R w := by
  have hcl : ∀ w, Subgroup.closure (Submodule.localBoxUnits R w) = localUnits hR w := fun w => (localUnits hR w).closure_eq
  simp only [awayUnits, Subgroup.mem_iInf, Subgroup.mem_comap, hcl]
  rfl

end Scalar21

namespace Scalar21

variable {a b : ℚ}

open CerednikDrinfeld.CosetGraph

def coord (w : HeightOneSpectrum (𝓞 ℚ)) :
    ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b] :=
  (QuaternionAlgebra.baseChangeRight (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    rfl (map_zero _) rfl).toRingEquiv

theorem coord_formula (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ) :
    coord w (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) := by
  show QuaternionAlgebra.baseChangeRight _ _ _ (z ⊗ₜ[ℚ] r) = _
  rw [QuaternionAlgebra.baseChangeRight_tmul]
  ext <;> simp [smul_eq_mul]

def locNrd (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : w.adicCompletion ℚ :=
  QuaternionAlgebra.nrd (coord w x)

theorem nrd_mul' {K : Type*} [CommRing K] {a' b' : K} (x y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem locNrd_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    locNrd w (x * y) = locNrd w x * locNrd w y := by
  unfold locNrd
  rw [(coord w).map_mul, nrd_mul']

theorem locNrd_one (w : HeightOneSpectrum (𝓞 ℚ)) : locNrd w (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 1 := by
  unfold locNrd
  have h1 : coord w (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 1 := map_one (coord w)
  rw [h1, QuaternionAlgebra.nrd_one]

theorem locNrd_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    locNrd w (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd z) := by
  unfold locNrd
  rw [coord_formula, one_smul, QuaternionAlgebra.nrd_mk, QuaternionAlgebra.nrd]
  simp only [map_sub, map_add, map_mul, map_pow]

theorem locNrd_one_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (t : w.adicCompletion ℚ) :
    locNrd w ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t ^ 2 := by
  unfold locNrd
  rw [coord_formula, QuaternionAlgebra.smul_mk, QuaternionAlgebra.nrd_mk]
  simp only [show (1 : ℍ[ℚ, a, b]).re = 1 from rfl, show (1 : ℍ[ℚ, a, b]).imI = 0 from rfl,
    show (1 : ℍ[ℚ, a, b]).imJ = 0 from rfl, show (1 : ℍ[ℚ, a, b]).imK = 0 from rfl, map_one, map_zero,
    smul_eq_mul, mul_one, mul_zero]
  ring

theorem ratSmul_eq (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) * x := by
  have e1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) = c • (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rw [e1, smul_mul_assoc, one_mul]

theorem locNrd_ratSmul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    locNrd w (c • x) = algebraMap ℚ (w.adicCompletion ℚ) c ^ 2 * locNrd w x := by
  rw [ratSmul_eq, locNrd_mul, locNrd_one_tmul]

theorem locNrd_conj (w : HeightOneSpectrum (𝓞 ℚ)) {g gi : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hg : gi * g = 1)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : locNrd w (gi * x * g) = locNrd w x := by
  rw [locNrd_mul, locNrd_mul, mul_comm (locNrd w gi), mul_assoc, ← locNrd_mul, hg, locNrd_one, mul_one]

section Div
variable {p : ℕ} [Fact p.Prime]

theorem mem_localBox_iff_locNrd (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox R v ↔ locNrd v x ∈ v.adicCompletionIntegers ℚ := by
  have hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y := (hdef.2.2 v).mpr hv
  obtain ⟨Λ₁, Λ₂, h₁, h₂, hRdef, -⟩ := hR
  have hbox : Submodule.localBox R v = Submodule.localBox Λ₁ v := by
    rw [hRdef, Submodule.localBox_inf Λ₁ Λ₂ h₁.isOrder.fg h₁.isOrder.spanTop h₂.isOrder.fg h₂.isOrder.spanTop,
      ← QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v hdiv h₁ h₂, inf_idem]
  rw [hbox]
  exact QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit h₁ v hdiv
    (coord v) (coord_formula v) x

end Div

end Scalar21

namespace Scalar21

variable {a b : ℚ}

open CerednikDrinfeld.CosetGraph

theorem mat_smul_mul {v : HeightOneSpectrum (𝓞 ℚ)} (c : v.adicCompletion ℚ)
    (M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : (c • M) * N = c • (M * N) := by
  ext i j : 1
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cayley_hamilton_two {v : HeightOneSpectrum (𝓞 ℚ)} (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    X * X = X.trace • X - X.det • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  ext i j : 1
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem mul_self_eq' {K : Type*} [CommRing K] {a' b' : K} (x : ℍ[K, a', b']) :
    x * x = (QuaternionAlgebra.trd x) • x - (QuaternionAlgebra.nrd x) • (1 : ℍ[K, a', b']) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd, QuaternionAlgebra.trd] <;> ring

section LocalDetNrd

variable {v : HeightOneSpectrum (𝓞 ℚ)}
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
  (hφ : ∀ t : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
  (ψ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
  (hψ : ∀ (z : ℍ[ℚ, a, b]) (t : v.adicCompletion ℚ),
      ψ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re,
        algebraMap ℚ (v.adicCompletion ℚ) z.imI, algebraMap ℚ (v.adicCompletion ℚ) z.imJ,
        algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))

include hψ in
theorem psi_one_tmul (t : v.adicCompletion ℚ) :
    ψ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) =
      ((t : v.adicCompletion ℚ) : ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) := by
  rw [hψ]
  ext <;> simp

include hψ in

theorem symm_smul (t : v.adicCompletion ℚ)
    (ξ : ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) :
    ψ.symm (t • ξ) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) * ψ.symm ξ := by
  apply ψ.injective
  rw [ψ.apply_symm_apply, ψ.map_mul, psi_one_tmul ψ hψ, ψ.apply_symm_apply, QuaternionAlgebra.coe_mul_eq_smul]

include hφ hψ in

theorem det_eq_nrd (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    (φ x).det = QuaternionAlgebra.nrd (ψ x) := by
  set ξ := ψ x with hξ
  have hx : x = ψ.symm ξ := by rw [hξ, ψ.symm_apply_apply]

  have hrel : φ x * φ x = QuaternionAlgebra.trd ξ • φ x - QuaternionAlgebra.nrd ξ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    have h0 : x * x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] QuaternionAlgebra.trd ξ) * x - ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] QuaternionAlgebra.nrd ξ) := by
      have := congrArg ψ.symm (mul_self_eq' ξ)
      rw [ψ.symm.map_mul, ψ.symm.map_sub, symm_smul ψ hψ, symm_smul ψ hψ, ψ.symm.map_one, mul_one, ← hx] at this
      exact this
    rw [← φ.map_mul, h0, φ.map_sub, φ.map_mul, hφ, hφ, mat_smul_mul, one_mul]
  have hCH := cayley_hamilton_two (φ x)
  have hdiff : (QuaternionAlgebra.trd ξ - (φ x).trace) • φ x =
      (QuaternionAlgebra.nrd ξ - (φ x).det) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_sub_eq_sub, ← hrel, ← hCH]
  by_cases hs : QuaternionAlgebra.trd ξ - (φ x).trace = 0
  · rw [hs, zero_smul] at hdiff
    have h00 := congrFun (congrFun hdiff 0) 0
    simp only [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    exact (sub_eq_zero.mp h00.symm).symm
  ·
    have hXs : φ x = ((QuaternionAlgebra.trd ξ - (φ x).trace)⁻¹ * (QuaternionAlgebra.nrd ξ - (φ x).det)) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) => (QuaternionAlgebra.trd ξ - (φ x).trace)⁻¹ • M) hdiff
      simp only [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
      exact this
    obtain ⟨c, hc⟩ : ∃ c : v.adicCompletion ℚ, φ x = c • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := ⟨_, hXs⟩
    have hx1 : x = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c := by
      apply φ.injective; rw [hc, hφ]
    have hξc : ξ = ((c : v.adicCompletion ℚ) : ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a,
        algebraMap ℚ (v.adicCompletion ℚ) b]) := by rw [hξ, hx1, psi_one_tmul ψ hψ]
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hξc, QuaternionAlgebra.nrd_coe]

end LocalDetNrd

theorem det_eq_nrd_coord {v : HeightOneSpectrum (𝓞 ℚ)}
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ t : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    (φ x).det = locNrd v x :=
  det_eq_nrd φ hφ (coord v) (coord_formula v) x

end Scalar21

namespace Scalar21

variable {a b : ℚ}

open CerednikDrinfeld.CosetGraph

theorem val_toLoc (u : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) :
    ((toLoc u γ : (Loc a b u)ˣ) : Loc a b u) = (γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) := rfl

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (w : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ w ≤ Submodule.localBox Λ' w := by
  unfold Submodule.localBox
  exact AddSubgroup.closure_mono fun x ⟨z, hz, c, hc, e⟩ => ⟨z, h hz, c, hc, e⟩

theorem nrd_units_ne_zero (γ : (ℍ[ℚ, a, b])ˣ) : QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]) ≠ 0 := by
  intro h
  have := nrd_mul' (γ : ℍ[ℚ, a, b]) ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, QuaternionAlgebra.nrd_one, h, zero_mul] at this
  exact one_ne_zero this

theorem nrd_units_inv (γ : (ℍ[ℚ, a, b])ˣ) :
    QuaternionAlgebra.nrd ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]))⁻¹ := by
  have hm := nrd_mul' (γ : ℍ[ℚ, a, b]) ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, QuaternionAlgebra.nrd_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

theorem det_mem_integers {v : HeightOneSpectrum (𝓞 ℚ)} (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ) : M.det ∈ v.adicCompletionIntegers ℚ := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

theorem isEichlerOrder_one_of_isMaximalOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) :
    QuaternionAlgebra.IsEichlerOrder Λ 1 :=
  ⟨Λ, Λ, hΛ, hΛ, (inf_idem Λ).symm, AddSubgroup.relIndex_self _⟩

theorem v_eq_one_of_mem_of_inv_mem {v : HeightOneSpectrum (𝓞 ℚ)} {t : v.adicCompletion ℚ}
    (h1 : t ∈ v.adicCompletionIntegers ℚ) (h2 : t⁻¹ ∈ v.adicCompletionIntegers ℚ) (ht : t ≠ 0) : Valued.v t = 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [map_inv₀] at h2
  have h0 : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht
  have h3 : 1 ≤ Valued.v t := by rwa [inv_le_one₀ (zero_lt_iff.mpr h0)] at h2
  exact le_antisymm h1 h3

theorem v_nrd_eq_one_of_toLoc_mem_localBoxUnits {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    (γ : (ℍ[ℚ, a, b])ˣ) (hγ : toLoc w γ ∈ Submodule.localBoxUnits Λ w) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]))) = 1 := by
  classical
  have hq' : q'.Prime := Fact.out
  have hn0 : algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b])) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective]; exact nrd_units_ne_zero γ
  have hinvval : algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) =
      (algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b])))⁻¹ := by
    rw [nrd_units_inv, map_inv₀]
  have hγ1 : ((γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox Λ w := by rw [← val_toLoc]; exact hγ.1
  have hγ2 : (((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox Λ w := by
    rw [← val_toLoc, map_inv]; exact hγ.2
  by_cases hw : ((q' : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
  ·
    have hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, y ≠ 0 → IsUnit y := (hdef.2.2 w).mpr hw
    have e := fun x => QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit hΛ w hdiv
      (coord w) (coord_formula w) x
    have h1 := (e _).mp hγ1
    have h2 := (e _).mp hγ2
    change locNrd w _ ∈ _ at h1
    change locNrd w _ ∈ _ at h2
    rw [locNrd_tmul_one] at h1 h2
    rw [hinvval] at h2
    exact v_eq_one_of_mem_of_inv_mem h1 h2 hn0
  ·
    have h1w : ((1 : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      rw [Nat.cast_one]; exact fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    obtain ⟨φ, hφ, hφΛ⟩ := QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef
      (isEichlerOrder_one_of_isMaximalOrder hΛ) w hw h1w
    have d1 := det_mem_integers _ ((hφΛ _).mp hγ1)
    have d2 := det_mem_integers _ ((hφΛ _).mp hγ2)
    rw [det_eq_nrd_coord φ hφ, locNrd_tmul_one] at d1 d2
    rw [hinvval] at d2
    exact v_eq_one_of_mem_of_inv_mem d1 d2 hn0

end Scalar21

namespace Scalar21

variable {a b : ℚ}

open CerednikDrinfeld.CosetGraph

theorem eq_one_of_sq_eq_one {t : WithZero (Multiplicative ℤ)} (ht : t ≠ 0) (h : t * t = 1) : t = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, t = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    ⟨Multiplicative.toAdd (WithZero.unzero ht), by rw [ofAdd_toAdd, WithZero.coe_unzero]⟩
  rw [hm, ← WithZero.coe_mul, ← ofAdd_add, ← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_inj] at h
  have : m + m = 0 := Multiplicative.ofAdd.injective h
  have hm0 : m = 0 := by omega
  rw [hm, hm0, ofAdd_zero, WithZero.coe_one]

theorem mem_of_scalar {p q' : ℕ} [Fact p.Prime] [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (Γ : Subgroup (ℍ[ℚ, a, b])ˣ)
    (hΓ0 : ∀ x : (ℍ[ℚ, a, b])ˣ, x ∈ Γ ↔ x ∈ awayUnits R v ∧ Even (padicValRat p (QuaternionAlgebra.nrd (x : ℍ[ℚ, a, b]))))
    (z : (ℍ[ℚ, a, b])ˣ) (hz : ∃ c : ℚ, c ≠ 0 ∧ (z : ℍ[ℚ, a, b]) = algebraMap ℚ (ℍ[ℚ, a, b]) c)
    (hprod : ∃ δ ∈ Γ, ∃ γ ∈ Γ, ∃ t : (ℍ[ℚ, a, b])ˣ, z = δ * (t⁻¹ * γ * t)) : z ∈ Γ := by
  classical
  obtain ⟨c, hc0, hzc⟩ := hz
  obtain ⟨δ, hδ, γ, hγ, t, hzt⟩ := hprod
  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder
  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.isOrder
  rw [hΓ0] at hδ hγ ⊢
  have hnz : QuaternionAlgebra.nrd (z : ℍ[ℚ, a, b]) = c ^ 2 := by
    rw [hzc]
    exact QuaternionAlgebra.nrd_coe c

  have hnprod : QuaternionAlgebra.nrd (z : ℍ[ℚ, a, b]) =
      QuaternionAlgebra.nrd (δ : ℍ[ℚ, a, b]) * QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]) := by
    rw [hzt, Units.val_mul, Units.val_mul, Units.val_mul, nrd_mul', nrd_mul', nrd_mul', nrd_units_inv]
    congr 1
    rw [mul_comm (QuaternionAlgebra.nrd ((t : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]))⁻¹, mul_assoc,
      inv_mul_cancel₀ (nrd_units_ne_zero t), mul_one]
  refine ⟨?_, ?_⟩
  ·
    rw [mem_awayUnits_iff hRo]
    intro w hw
    have hδw := ((mem_awayUnits_iff hRo v δ).mp hδ.1) w hw
    have hγw := ((mem_awayUnits_iff hRo v γ).mp hγ.1) w hw
    have hδΛ : toLoc w δ ∈ Submodule.localBoxUnits Λ w := ⟨localBox_mono hRΛ w hδw.1, localBox_mono hRΛ w hδw.2⟩
    have hγΛ : toLoc w γ ∈ Submodule.localBoxUnits Λ w := ⟨localBox_mono hRΛ w hγw.1, localBox_mono hRΛ w hγw.2⟩
    have v1 := v_nrd_eq_one_of_toLoc_mem_localBoxUnits hdef hΛ w δ hδΛ
    have v2 := v_nrd_eq_one_of_toLoc_mem_localBoxUnits hdef hΛ w γ hγΛ
    have hvc : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) c) = 1 := by
      have h : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) c) * Valued.v (algebraMap ℚ (w.adicCompletion ℚ) c) = 1 := by
        rw [← map_mul, ← map_mul, ← pow_two, ← hnz, hnprod, map_mul, map_mul, v1, v2, one_mul]
      have hc0' : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) c) ≠ 0 := by
        rw [Valuation.ne_zero_iff, Ne, map_eq_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective]; exact hc0
      exact eq_one_of_sq_eq_one hc0' h
    have hcO : algebraMap ℚ (w.adicCompletion ℚ) c ∈ w.adicCompletionIntegers ℚ := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hvc]
    have hciO : algebraMap ℚ (w.adicCompletion ℚ) c⁻¹ ∈ w.adicCompletionIntegers ℚ := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, hvc, inv_one]
    have hval : ((toLoc w z : (Loc a b w)ˣ) : Loc a b w) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c := by
      rw [val_toLoc, hzc, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    have hzinv : ((z⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = algebraMap ℚ (ℍ[ℚ, a, b]) c⁻¹ :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hzc, ← map_mul, mul_inv_cancel₀ hc0, map_one])
    have hvali : (((toLoc w z)⁻¹ : (Loc a b w)ˣ) : Loc a b w) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c⁻¹ := by
      rw [← map_inv, val_toLoc, hzinv, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    refine ⟨?_, ?_⟩
    · rw [hval]; unfold Submodule.localBox; exact AddSubgroup.subset_closure ⟨1, hRo.one_mem, _, hcO, rfl⟩
    · rw [hvali]; unfold Submodule.localBox; exact AddSubgroup.subset_closure ⟨1, hRo.one_mem, _, hciO, rfl⟩
  ·
    rw [hnprod, padicValRat.mul (nrd_units_ne_zero δ) (nrd_units_ne_zero γ)]
    exact hδ.2.add hγ.2

end Scalar21

end

theorem solution

    {a₁ b₁ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₁ : IsDefiniteRamifiedExactlyAt a₁ b₁ q')
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((q : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)

    (Γ : Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))))
    (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : ∃ c : ℚ, c ≠ 0 ∧ (z : ℍ[ℚ, a₁, b₁]) = algebraMap ℚ (ℍ[ℚ, a₁, b₁]) c)
    (hprod : ∃ δ ∈ Γ, ∃ γ ∈ Γ, ∃ t : (ℍ[ℚ, a₁, b₁])ˣ, z = δ * (t⁻¹ * γ * t)) :
    z ∈ Γ :=
  Scalar21.mem_of_scalar hdef₁ hΛ₁ hR₁ hRΛ₁ v₂ Γ hΓ0 z hz hprod

end S_CerednikDrinfeld_CosetGraph_mem_of_eq_algebraMap_of_eq_mul_conj
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_mem_of_eq_algebraMap_of_eq_mul_conj (solution)
