-- Prove2me | solution 1 for GaloisLattice.exists_trace_det_of_basis_fin_two_of_frobenius_relations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/cf344287-64bb-519c-a512-ed500093297d

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisLattice_exists_trace_det_of_basis_fin_two_of_frobenius_relations
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

open scoped TensorProduct

set_option autoImplicit false

namespace TrDetPkg

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T]

abbrev V (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] : Type :=
  ℚ_[p] ⊗[ℤ_[p]] T

noncomputable def toV (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] :
    T →ₗ[ℤ_[p]] V p T :=
  TensorProduct.mk ℤ_[p] ℚ_[p] T 1

theorem toV_apply (x : T) : toV p T x = (1 : ℚ_[p]) ⊗ₜ x := rfl

theorem toV_smul (z : ℤ_[p]) (x : T) : toV p T (z • x) = (z : ℚ_[p]) • toV p T x := by
  rw [LinearMap.map_smul]
  exact (algebraMap_smul ℚ_[p] z (toV p T x)).symm

noncomputable abbrev bc (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] :
    Module.End ℤ_[p] T →ₐ[ℤ_[p]] Module.End ℚ_[p] (V p T) :=
  Module.End.baseChangeHom ℤ_[p] ℚ_[p] T

theorem bc_toV (f : Module.End ℤ_[p] T) (x : T) : bc p T f (toV p T x) = toV p T (f x) := rfl

theorem bc_tmul (f : Module.End ℤ_[p] T) (a : ℚ_[p]) (x : T) :
    bc p T f (a ⊗ₜ x) = a ⊗ₜ (f x) := rfl

theorem bc_apply (f : Module.End ℤ_[p] T) : bc p T f = f.baseChange ℚ_[p] := rfl

section inj
variable [Module.Free ℤ_[p] T]

theorem toV_injective : Function.Injective (toV p T) := by
  have h1 : Function.Injective (Algebra.linearMap ℤ_[p] ℚ_[p]) :=
    IsFractionRing.injective ℤ_[p] ℚ_[p]
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := T)
    (Algebra.linearMap ℤ_[p] ℚ_[p]) h1
  intro x y hxy
  have : (Algebra.linearMap ℤ_[p] ℚ_[p]).rTensor T ((TensorProduct.lid ℤ_[p] T).symm x) =
      (Algebra.linearMap ℤ_[p] ℚ_[p]).rTensor T ((TensorProduct.lid ℤ_[p] T).symm y) := by
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply,
      map_one]
    exact hxy
  exact (TensorProduct.lid ℤ_[p] T).symm.injective (h2 this)

theorem bc_injective : Function.Injective (bc p T) := by
  intro f g hfg
  ext x
  apply toV_injective (p := p)
  rw [← bc_toV, ← bc_toV, hfg]

end inj

theorem exists_pow_mul_eq_coe (a : ℚ_[p]) : ∃ (k : ℕ) (z : ℤ_[p]), (p : ℚ_[p]) ^ k * a = z := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖a‖ ≤ (p : ℝ) ^ k := by
    have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖a‖ hp
    exact ⟨k, hk.le⟩
  have hnorm : ‖(p : ℚ_[p]) ^ k * a‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Padic.norm_p]
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    rw [inv_pow, ← div_eq_inv_mul, div_le_one (pow_pos hp0 k)]
    exact hk
  exact ⟨k, ⟨_, hnorm⟩, rfl⟩

theorem exists_pow_smul_eq_toV (v : V p T) :
    ∃ (k : ℕ) (x : T), ((p : ℚ_[p]) ^ k) • v = toV p T x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by rw [map_zero, smul_zero]⟩
  | tmul a x =>
    obtain ⟨k, z, hz⟩ := exists_pow_mul_eq_coe (p := p) a
    refine ⟨k, z • x, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, hz, toV_smul, toV_apply,
      TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
    rfl
  | add v w hv hw =>
    obtain ⟨k, x, hx⟩ := hv
    obtain ⟨j, y, hy⟩ := hw
    refine ⟨k + j, ((p : ℤ_[p]) ^ j) • x + ((p : ℤ_[p]) ^ k) • y, ?_⟩
    have e1 : ((p : ℚ_[p]) ^ (k + j)) • v = toV p T (((p : ℤ_[p]) ^ j) • x) := by
      rw [toV_smul, ← hx, smul_smul, pow_add, mul_comm]
      simp
    have e2 : ((p : ℚ_[p]) ^ (k + j)) • w = toV p T (((p : ℤ_[p]) ^ k) • y) := by
      rw [toV_smul, ← hy, smul_smul, pow_add]
      simp
    rw [smul_add, map_add, e1, e2]

end TrDetPkg

namespace TrDetPkg

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T]
variable {ι₀ : Type} (A : ι₀ → Module.End ℤ_[p] T)

noncomputable def R (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T]
    (A : ι₀ → Module.End ℤ_[p] T) : Subalgebra ℚ_[p] (Module.End ℚ_[p] (V p T)) :=
  Algebra.adjoin ℚ_[p] (Set.range fun g : ι₀ => (A g).baseChange ℚ_[p])

theorem bc_mem_R (i : ι₀) : bc p T (A i) ∈ R p T A :=
  Algebra.subset_adjoin ⟨i, rfl⟩

variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]

noncomputable def ψ (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T]
    (𝕋 : Type) [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T] :
    𝕋 →ₐ[ℤ_[p]] Module.End ℚ_[p] (V p T) :=
  (bc p T).comp (Algebra.lsmul ℤ_[p] ℤ_[p] T)

theorem ψ_apply (t : 𝕋) : ψ p T 𝕋 t = bc p T (Algebra.lsmul ℤ_[p] ℤ_[p] T t) := rfl

theorem ψ_tmul (t : 𝕋) (a : ℚ_[p]) (x : T) : ψ p T 𝕋 t (a ⊗ₜ x) = a ⊗ₜ (t • x) := rfl

theorem ψ_toV (t : 𝕋) (x : T) : ψ p T 𝕋 t (toV p T x) = toV p T (t • x) := rfl

theorem ψ_injective [Module.Free ℤ_[p] T] (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0) :
    Function.Injective (ψ p T 𝕋) := by
  intro s t hst
  have h := bc_injective hst
  rw [← sub_eq_zero]
  refine hfaith _ fun x => ?_
  have := LinearMap.congr_fun h x
  change s • x = t • x at this
  rw [sub_smul, this, sub_self]

variable (op : ι₀ → 𝕋)

theorem ψ_op (hop : ∀ (g : ι₀) (x : T), op g • x = A g x) (g : ι₀) :
    ψ p T 𝕋 (op g) = bc p T (A g) := by
  rw [ψ_apply]
  congr 1
  exact LinearMap.ext (hop g)

theorem ψ_mem_R (hop : ∀ (g : ι₀) (x : T), op g • x = A g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤) (t : 𝕋) : ψ p T 𝕋 t ∈ R p T A := by
  have ht : t ∈ Algebra.adjoin ℤ_[p] (Set.range op) := by rw [hgen]; exact Algebra.mem_top
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [ψ_op A op hop]
    exact bc_mem_R A g
  | algebraMap r =>
    rw [AlgHom.commutes]
    have : algebraMap ℤ_[p] (Module.End ℚ_[p] (V p T)) r =
        algebraMap ℚ_[p] (Module.End ℚ_[p] (V p T)) (r : ℚ_[p]) :=
      IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] _ r
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

theorem isMulCommutative_R (hop : ∀ (g : ι₀) (x : T), op g • x = A g x) :
    IsMulCommutative (R p T A) := by
  refine Algebra.isMulCommutative_adjoin ℚ_[p] ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  show bc p T (A i) * bc p T (A j) = bc p T (A j) * bc p T (A i)
  rw [← ψ_op A op hop, ← ψ_op A op hop, ← map_mul, ← map_mul, mul_comm]

theorem pow_smul_ψ (n : ℕ) (u : 𝕋) :
    ((p : ℚ_[p]) ^ n) • ψ p T 𝕋 u = ψ p T 𝕋 (((p : ℤ_[p]) ^ n) • u) := by
  rw [map_smul, ← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ n) (ψ p T 𝕋 u), map_pow, map_natCast]

theorem exists_pow_smul_eq_ψ (hop : ∀ (g : ι₀) (x : T), op g • x = A g x)
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) :
    ∃ (c : ℕ) (t : 𝕋), ((p : ℚ_[p]) ^ c) • r = ψ p T 𝕋 t := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨0, op g, by rw [pow_zero, one_smul, ψ_op A op hop]; rfl⟩
  | algebraMap a =>
    obtain ⟨k, z, hz⟩ := exists_pow_mul_eq_coe (p := p) a
    refine ⟨k, algebraMap ℤ_[p] 𝕋 z, ?_⟩
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul,
      hz]
    exact (algebraMap_smul ℚ_[p] z (1 : Module.End ℚ_[p] (V p T))).symm
  | add x y _ _ hx hy =>
    obtain ⟨c, s, hs⟩ := hx
    obtain ⟨d, t, ht⟩ := hy
    refine ⟨c + d, ((p : ℤ_[p]) ^ d) • s + ((p : ℤ_[p]) ^ c) • t, ?_⟩
    rw [map_add, ← pow_smul_ψ, ← pow_smul_ψ, ← hs, ← ht, smul_smul, smul_smul, ← pow_add,
      ← pow_add, add_comm d c, smul_add]
  | mul x y _ _ hx hy =>
    obtain ⟨c, s, hs⟩ := hx
    obtain ⟨d, t, ht⟩ := hy
    refine ⟨c + d, s * t, ?_⟩
    rw [map_mul, ← hs, ← ht, pow_add, smul_mul_smul_comm]

end TrDetPkg

namespace TrDetPkg

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T]
variable {ι₀ : Type} {A : ι₀ → Module.End ℤ_[p] T}
variable {G : Type} [Group G] (ρ : G →* Module.End ℤ_[p] T)

noncomputable abbrev ρV (σ : G) : Module.End ℚ_[p] (V p T) := bc p T (ρ σ)

theorem ρV_mul (σ τ : G) : ρV ρ (σ * τ) = ρV ρ σ * ρV ρ τ := by
  rw [ρV, map_mul, map_mul]

theorem ρV_one : ρV ρ (1 : G) = 1 := by rw [ρV, map_one, map_one]

theorem ρV_mul_inv (σ : G) : ρV ρ σ * ρV ρ σ⁻¹ = 1 := by rw [← ρV_mul, mul_inv_cancel, ρV_one]

theorem ρV_inv_mul (σ : G) : ρV ρ σ⁻¹ * ρV ρ σ = 1 := by rw [← ρV_mul, inv_mul_cancel, ρV_one]

variable (A)

theorem commute_ρV (hcomm : ∀ (σ : G) (g : ι₀) (x : T), ρ σ (A g x) = A g (ρ σ x)) (σ : G)
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) : r * ρV ρ σ = ρV ρ σ * r := by
  have hle : R p T A ≤ Subalgebra.centralizer ℚ_[p] {ρV ρ σ} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩ _ rfl
    show ρV ρ σ * bc p T (A i) = bc p T (A i) * ρV ρ σ
    rw [ρV, ← map_mul, ← map_mul]
    congr 1
    exact LinearMap.ext fun x => hcomm σ i x
  exact (Subalgebra.mem_centralizer_iff ℚ_[p]).mp (hle hr) _ rfl |>.symm

noncomputable def ρR (hcomm : ∀ (σ : G) (g : ι₀) (x : T), ρ σ (A g x) = A g (ρ σ x)) (σ : G) :
    V p T →ₗ[R p T A] V p T where
  toFun := ρV ρ σ
  map_add' := map_add _
  map_smul' r v := by
    show ρV ρ σ ((r : Module.End ℚ_[p] (V p T)) v) = (r : Module.End ℚ_[p] (V p T)) (ρV ρ σ v)
    rw [← Module.End.mul_apply, ← commute_ρV A ρ hcomm σ r.2, Module.End.mul_apply]

variable {A ρ}
variable {hcomm : ∀ (σ : G) (g : ι₀) (x : T), ρ σ (A g x) = A g (ρ σ x)}

theorem ρR_apply (σ : G) (v : V p T) : ρR A ρ hcomm σ v = ρV ρ σ v := rfl

theorem ρR_mul (σ τ : G) : ρR A ρ hcomm (σ * τ) = ρR A ρ hcomm σ * ρR A ρ hcomm τ :=
  LinearMap.ext fun v => by
    rw [Module.End.mul_apply, ρR_apply, ρR_apply, ρR_apply, ρV_mul, Module.End.mul_apply]

theorem ρR_one : ρR A ρ hcomm 1 = 1 :=
  LinearMap.ext fun v => by rw [ρR_apply, ρV_one]; rfl

section Matrices

open scoped IsMulCommutative

variable [IsMulCommutative (R p T A)] (b : Module.Basis (Fin 2) (R p T A) (V p T))

noncomputable def Mat (σ : G) : Matrix (Fin 2) (Fin 2) (R p T A) :=
  LinearMap.toMatrix b b (ρR A ρ hcomm σ)

theorem Mat_apply (σ : G) (i j : Fin 2) :
    Mat (hcomm := hcomm) b σ i j = b.repr (ρV ρ σ (b j)) i :=
  LinearMap.toMatrix_apply b b _ i j

theorem Mat_mul (σ τ : G) :
    Mat (hcomm := hcomm) b (σ * τ) = Mat (hcomm := hcomm) b σ * Mat (hcomm := hcomm) b τ := by
  rw [Mat, ρR_mul, LinearMap.toMatrix_mul]; rfl

theorem Mat_one : Mat (hcomm := hcomm) b (1 : G) = 1 := by
  rw [Mat, ρR_one]
  exact LinearMap.toMatrix_one b

noncomputable def tr (σ : G) : R p T A := (Mat (hcomm := hcomm) b σ).trace

noncomputable def dt (σ : G) : R p T A := (Mat (hcomm := hcomm) b σ).det

theorem tr_one : tr (hcomm := hcomm) b (1 : G) = 2 := by
  rw [tr, Mat_one, Matrix.trace_one, Fintype.card_fin]; rfl

theorem dt_one : dt (hcomm := hcomm) b (1 : G) = 1 := by
  rw [dt, Mat_one, Matrix.det_one]

theorem dt_mul (σ τ : G) :
    dt (hcomm := hcomm) b (σ * τ) = dt (hcomm := hcomm) b σ * dt (hcomm := hcomm) b τ := by
  rw [dt, Mat_mul, Matrix.det_mul]; rfl

theorem tr_conj (σ τ : G) : tr (hcomm := hcomm) b (σ * τ * σ⁻¹) = tr (hcomm := hcomm) b τ := by
  rw [tr, tr, Mat_mul, Mat_mul, Matrix.trace_mul_cycle, ← Mat_mul, inv_mul_cancel, Mat_one,
    Matrix.one_mul]

theorem dt_conj (σ τ : G) : dt (hcomm := hcomm) b (σ * τ * σ⁻¹) = dt (hcomm := hcomm) b τ := by
  rw [dt_mul, dt_mul, mul_comm, ← mul_assoc, ← dt_mul, inv_mul_cancel, dt_one, one_mul]

theorem trace_mul_self_fin_two {C : Type} [CommRing C] (N : Matrix (Fin 2) (Fin 2) C) :
    (N * N).trace = N.trace * N.trace - 2 * N.det := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  ring

theorem cayleyHamilton_fin_two {C : Type} [CommRing C] (N : Matrix (Fin 2) (Fin 2) C) :
    N * N - N.trace • N + N.det • (1 : Matrix (Fin 2) (Fin 2) C) = 0 := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cayleyHamilton_fin_two_apply {C : Type} [CommRing C] (N : Matrix (Fin 2) (Fin 2) C)
    (i j : Fin 2) : (N * N) i j - N.trace * N i j + N.det * (1 : Matrix (Fin 2) (Fin 2) C) i j = 0 := by
  have h := congrFun (congrFun (cayleyHamilton_fin_two N) i) j
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_mul, Matrix.zero_apply] at h
  exact h

theorem tr_mul_self (σ : G) :
    tr (hcomm := hcomm) b σ * tr (hcomm := hcomm) b σ =
      tr (hcomm := hcomm) b (σ * σ) + 2 * dt (hcomm := hcomm) b σ := by
  have h := trace_mul_self_fin_two (Mat (hcomm := hcomm) b σ)
  rw [tr, tr, dt, Mat_mul, h]
  ring

theorem apply_basis_eq_sum (f : V p T →ₗ[R p T A] V p T) (j : Fin 2) :
    f (b j) = ∑ i, (LinearMap.toMatrix b b f i j) • b i := by
  conv_lhs => rw [← Matrix.toLin_toMatrix b b f]
  rw [Matrix.toLin_self]

theorem mul_comm_R (r s : R p T A) : r * s = s * r :=
  mul_comm r s

theorem cayleyHamilton_ρV (σ : G) :
    ρV ρ σ * ρV ρ σ - (tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) * ρV ρ σ
      + (dt (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) = 0 := by
  set E : Module.End ℚ_[p] (V p T) := ρV ρ σ * ρV ρ σ
      - (tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) * ρV ρ σ
      + (dt (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) with hE

  have hcommE : ∀ r : R p T A, (r : Module.End ℚ_[p] (V p T)) * E = E * r := by
    intro r
    have h1 : (r : Module.End ℚ_[p] (V p T)) * ρV ρ σ = ρV ρ σ * r := commute_ρV A ρ hcomm σ r.2
    have h2 : (r : Module.End ℚ_[p] (V p T)) * (tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T))
        = (tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) * r :=
      congrArg Subtype.val (mul_comm_R r (tr (hcomm := hcomm) b σ))
    have h3 : (r : Module.End ℚ_[p] (V p T)) * (dt (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T))
        = (dt (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) * r :=
      congrArg Subtype.val (mul_comm_R r (dt (hcomm := hcomm) b σ))
    have ea : (r : Module.End ℚ_[p] (V p T)) * (ρV ρ σ * ρV ρ σ) = ρV ρ σ * ρV ρ σ * r := by
      rw [← mul_assoc, h1, mul_assoc, h1, ← mul_assoc]
    have eb : (r : Module.End ℚ_[p] (V p T))
        * ((tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) * ρV ρ σ)
        = (tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) * ρV ρ σ * r := by
      rw [← mul_assoc, h2, mul_assoc, h1, ← mul_assoc]
    rw [hE, mul_add, mul_sub, add_mul, sub_mul, ea, eb, h3]

  let ER : V p T →ₗ[R p T A] V p T :=
    { toFun := E
      map_add' := map_add E
      map_smul' := fun r v => by
        show E ((r : Module.End ℚ_[p] (V p T)) v) = (r : Module.End ℚ_[p] (V p T)) (E v)
        rw [← Module.End.mul_apply, ← hcommE, Module.End.mul_apply] }
  have hER : ER = 0 := by
    refine b.ext fun j => ?_
    rw [LinearMap.zero_apply]
    show E (b j) = 0
    have e1 : ρV ρ σ (b j) = ∑ i, (Mat (hcomm := hcomm) b σ i j) • b i :=
      apply_basis_eq_sum b (ρR A ρ hcomm σ) j
    have e2 : ρV ρ σ (ρV ρ σ (b j)) = ∑ i, ((Mat (hcomm := hcomm) b σ * Mat (hcomm := hcomm) b σ) i j) • b i := by
      rw [← Mat_mul, ← Module.End.mul_apply, ← ρV_mul]
      exact apply_basis_eq_sum b (ρR A ρ hcomm (σ * σ)) j
    have e3 : (tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) (ρV ρ σ (b j))
        = ∑ i, ((tr (hcomm := hcomm) b σ) * Mat (hcomm := hcomm) b σ i j) • b i := by
      rw [e1, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul]
      rfl
    have e4 : (dt (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) (b j)
        = ∑ i, ((dt (hcomm := hcomm) b σ) * (1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j) • b i := by
      have : (dt (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) (b j)
          = (dt (hcomm := hcomm) b σ) • b j := rfl
      rw [this, Finset.sum_eq_single j (fun i _ hij => by
        rw [Matrix.one_apply_ne hij, mul_zero, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h), Matrix.one_apply_eq, mul_one]
    have : E (b j) = ρV ρ σ (ρV ρ σ (b j)) - (tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) (ρV ρ σ (b j))
        + (dt (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) (b j) := rfl
    rw [this, e2, e3, e4, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    have key : ∀ (a c d : R p T A) (v : V p T), a • v - c • v + d • v = (a - c + d) • v :=
      fun a c d v =>
        calc a • v - c • v + d • v = (a - c) • v + d • v := congrArg (· + d • v) (sub_smul a c v).symm
          _ = (a - c + d) • v := (add_smul (a - c) d v).symm
    have hz : (Mat (hcomm := hcomm) b σ * Mat (hcomm := hcomm) b σ) i j
        - tr (hcomm := hcomm) b σ * Mat (hcomm := hcomm) b σ i j
        + dt (hcomm := hcomm) b σ * (1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j = 0 :=
      cayleyHamilton_fin_two_apply (Mat (hcomm := hcomm) b σ) i j
    rw [key, hz, zero_smul]
  refine LinearMap.ext fun v => ?_
  exact LinearMap.congr_fun hER v

end Matrices

end TrDetPkg

namespace TrDetPkg

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T]
variable {ι₀ : Type} {A : ι₀ → Module.End ℤ_[p] T}
variable {G : Type} [Group G] {ρ : G →* Module.End ℤ_[p] T}
variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]
variable {hcomm : ∀ (σ : G) (g : ι₀) (x : T), ρ σ (A g x) = A g (ρ σ x)}

section ES

open scoped IsMulCommutative

variable [IsMulCommutative (R p T A)] (b : Module.Basis (Fin 2) (R p T A) (V p T))

theorem quadratic_V (σ : G) (D T₀ : 𝕋) (ℓ : ℕ)
    (hES : ∀ x : T, D • ρ σ (ρ σ x) - T₀ • ρ σ x + ℓ • x = 0) :
    ψ p T 𝕋 D * ρV ρ σ * ρV ρ σ - ψ p T 𝕋 T₀ * ρV ρ σ
      + (ℓ : Module.End ℚ_[p] (V p T)) = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply]
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero, nsmul_zero, sub_zero, add_zero]
  | tmul a x =>
    rw [ρV, bc_tmul, bc_tmul, ψ_tmul, ψ_tmul, ← Nat.cast_smul_eq_nsmul ℤ_[p],
      ← TensorProduct.tmul_smul, Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_sub,
      ← TensorProduct.tmul_add, hES, TensorProduct.tmul_zero]
  | add v w hv hw =>
    rw [map_add, map_add, map_add, map_add, nsmul_add]
    rw [show ∀ a₁ a₂ b₁ b₂ c₁ c₂ : V p T,
        a₁ + a₂ - (b₁ + b₂) + (c₁ + c₂) = (a₁ - b₁ + c₁) + (a₂ - b₂ + c₂) from fun _ _ _ _ _ _ => by abel,
      hv, hw, add_zero]

theorem ψ_mul_tr_eq (σ : G) (D T₀ : 𝕋) (ℓ : ℕ)
    (hES : ∀ x : T, D • ρ σ (ρ σ x) - T₀ • ρ σ x + ℓ • x = 0)
    (hdet : ψ p T 𝕋 D * (dt (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T))
      = (ℓ : Module.End ℚ_[p] (V p T))) :
    ψ p T 𝕋 D * (tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) = ψ p T 𝕋 T₀ := by
  have hV := quadratic_V (ρ := ρ) σ D T₀ ℓ hES
  have hCH := cayleyHamilton_ρV (hcomm := hcomm) b σ
  set t : Module.End ℚ_[p] (V p T) := (tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T))
  set d : Module.End ℚ_[p] (V p T) := (dt (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T))
  have h1 : ρV ρ σ * ρV ρ σ = t * ρV ρ σ - d := by
    have h := hCH
    rw [add_eq_zero_iff_eq_neg, sub_eq_iff_eq_add] at h
    rw [h]
    abel
  rw [mul_assoc (ψ p T 𝕋 D) (ρV ρ σ) (ρV ρ σ), h1, mul_sub, ← mul_assoc, hdet] at hV
  have key : (ψ p T 𝕋 D * t - ψ p T 𝕋 T₀) * ρV ρ σ = 0 := by
    rw [sub_mul, ← hV]
    abel
  have : ψ p T 𝕋 D * t - ψ p T 𝕋 T₀ = 0 := by
    rw [← mul_one (ψ p T 𝕋 D * t - ψ p T 𝕋 T₀), ← ρV_mul_inv ρ σ, ← mul_assoc, key, zero_mul]
  exact sub_eq_zero.mp this

theorem cayleyHamilton_T [Module.Free ℤ_[p] T] (σ : G) (t d : 𝕋)
    (ht : (tr (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) = ψ p T 𝕋 t)
    (hd : (dt (hcomm := hcomm) b σ : Module.End ℚ_[p] (V p T)) = ψ p T 𝕋 d) (x : T) :
    ρ σ (ρ σ x) - t • ρ σ x + d • x = 0 := by
  apply toV_injective (p := p)
  have h := LinearMap.congr_fun (cayleyHamilton_ρV (hcomm := hcomm) b σ) (toV p T x)
  rw [ht, hd, LinearMap.zero_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, ρV, bc_toV, bc_toV, ψ_toV, ψ_toV] at h
  rw [map_add, map_sub, map_zero]
  exact h

end ES

section Unit

theorem exists_mul_eq_one_of_bijective [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
    (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0) (D : 𝕋)
    (hD : Function.Bijective fun x : T => D • x) : ∃ E : 𝕋, D * E = 1 := by
  classical
  let φ : 𝕋 →ₐ[ℤ_[p]] Module.End ℤ_[p] T := Algebra.lsmul ℤ_[p] ℤ_[p] T
  have hφ : Function.Injective φ := by
    intro s t hst
    rw [← sub_eq_zero]
    refine hfaith _ fun x => ?_
    have := LinearMap.congr_fun hst x
    change s • x = t • x at this
    rw [sub_smul, this, sub_self]
  let f : Module.End ℤ_[p] T := φ D
  have hf : Function.Bijective f := hD
  let e : T ≃ₗ[ℤ_[p]] T := LinearEquiv.ofBijective f hf
  have hdet : IsUnit (LinearMap.det f) := by
    have : (e : T →ₗ[ℤ_[p]] T) = f := rfl
    rw [← this, ← LinearEquiv.coe_det]
    exact Units.isUnit _
  set P := f.charpoly with hP
  have hc0 : IsUnit (P.coeff 0) := by
    have h := LinearMap.det_eq_sign_charpoly_coeff f
    rw [h] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  obtain ⟨u, hu⟩ := hc0

  have hCH : f * Polynomial.aeval f P.divX + algebraMap ℤ_[p] _ (P.coeff 0) = 0 := by
    have := LinearMap.aeval_self_charpoly f
    have e : P = Polynomial.X * P.divX + Polynomial.C (P.coeff 0) := (Polynomial.X_mul_divX_add P).symm
    rw [← hP, e, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at this
    exact this
  refine ⟨-((↑u⁻¹ : ℤ_[p]) • Polynomial.aeval D P.divX), hφ ?_⟩
  rw [map_one, map_mul, map_neg, map_smul, ← Polynomial.aeval_algHom_apply]
  show f * -((↑u⁻¹ : ℤ_[p]) • Polynomial.aeval f P.divX) = 1
  rw [mul_neg, mul_smul_comm, eq_neg_of_add_eq_zero_left hCH, smul_neg, neg_neg, ← hu,
    Algebra.algebraMap_eq_smul_one, smul_smul, Units.inv_mul, one_smul]

end Unit

end TrDetPkg

namespace TrDetPkg

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T]
variable {ι₀ : Type} {A : ι₀ → Module.End ℤ_[p] T}
variable {G : Type} [Group G] {ρ : G →* Module.End ℤ_[p] T}
variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]

section Theta

variable (p T 𝕋)

def Θ (c m : ℕ) (r : Module.End ℚ_[p] (V p T)) : Prop :=
  ∃ t : 𝕋, ((p : ℚ_[p]) ^ c) • r = ψ p T 𝕋 (((p : ℤ_[p]) ^ m) • t)

variable {p T 𝕋}

theorem Θ.zero (c m : ℕ) : Θ p T 𝕋 c m 0 :=
  ⟨0, by rw [smul_zero, smul_zero, map_zero]⟩

theorem Θ.add {c m : ℕ} {r s : Module.End ℚ_[p] (V p T)} (hr : Θ p T 𝕋 c m r)
    (hs : Θ p T 𝕋 c m s) : Θ p T 𝕋 c m (r + s) := by
  obtain ⟨t, ht⟩ := hr
  obtain ⟨u, hu⟩ := hs
  exact ⟨t + u, by rw [smul_add, ht, hu, smul_add, map_add]⟩

theorem Θ.neg {c m : ℕ} {r : Module.End ℚ_[p] (V p T)} (hr : Θ p T 𝕋 c m r) :
    Θ p T 𝕋 c m (-r) := by
  obtain ⟨t, ht⟩ := hr
  exact ⟨-t, by rw [smul_neg, ht, smul_neg, map_neg]⟩

theorem Θ.sub {c m : ℕ} {r s : Module.End ℚ_[p] (V p T)} (hr : Θ p T 𝕋 c m r)
    (hs : Θ p T 𝕋 c m s) : Θ p T 𝕋 c m (r - s) := by
  rw [sub_eq_add_neg]; exact hr.add hs.neg

theorem Θ.mul {c m c' m' : ℕ} {r s : Module.End ℚ_[p] (V p T)} (hr : Θ p T 𝕋 c m r)
    (hs : Θ p T 𝕋 c' m' s) : Θ p T 𝕋 (c + c') (m + m') (r * s) := by
  obtain ⟨t, ht⟩ := hr
  obtain ⟨u, hu⟩ := hs
  refine ⟨t * u, ?_⟩
  rw [pow_add, ← smul_mul_smul_comm, ht, hu, ← map_mul, pow_add, smul_mul_smul_comm]

theorem Θ.of_le {c c' m : ℕ} (h : c ≤ c') {r : Module.End ℚ_[p] (V p T)} (hr : Θ p T 𝕋 c m r) :
    Θ p T 𝕋 c' m r := by
  obtain ⟨t, ht⟩ := hr
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨((p : ℤ_[p]) ^ e) • t, ?_⟩
  rw [pow_add, mul_comm, mul_smul, ht, pow_smul_ψ, smul_comm]

theorem Θ.of_ge {c m m' : ℕ} (h : m' ≤ m) {r : Module.End ℚ_[p] (V p T)} (hr : Θ p T 𝕋 c m r) :
    Θ p T 𝕋 c m' r := by
  obtain ⟨t, ht⟩ := hr
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨((p : ℤ_[p]) ^ e) • t, ?_⟩
  rw [ht, pow_add, mul_smul]

theorem Θ.of_eq_ψ {r : Module.End ℚ_[p] (V p T)} {t : 𝕋} (h : r = ψ p T 𝕋 t) :
    Θ p T 𝕋 0 0 r := ⟨t, by rw [pow_zero, one_smul, pow_zero, one_smul, h]⟩

theorem Θ.cancel {N₀ m : ℕ} {r : Module.End ℚ_[p] (V p T)} (hr : Θ p T 𝕋 N₀ (m + N₀) r) :
    ∃ t : 𝕋, r = ψ p T 𝕋 (((p : ℤ_[p]) ^ m) • t) := by
  obtain ⟨t, ht⟩ := hr
  refine ⟨t, ?_⟩
  rw [pow_add, mul_comm, mul_smul, ← pow_smul_ψ] at ht
  have hp : ((p : ℚ_[p]) ^ N₀) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  exact smul_right_injective _ hp ht

end Theta

section Level

open scoped IsMulCommutative

variable [IsMulCommutative (R p T A)] (b : Module.Basis (Fin 2) (R p T A) (V p T))
variable {hcomm : ∀ (σ : G) (g : ι₀) (x : T), ρ σ (A g x) = A g (ρ σ x)}

omit [IsMulCommutative (R p T A)] in
theorem coe_smul_R (a : ℚ_[p]) (r : R p T A) :
    ((a • r : R p T A) : Module.End ℚ_[p] (V p T)) = a • (r : Module.End ℚ_[p] (V p T)) := rfl

omit [IsMulCommutative (R p T A)] in
theorem repr_smul_apply (a : ℚ_[p]) (v : V p T) (i : Fin 2) :
    b.repr (a • v) i = a • b.repr v i := by
  have h := LinearMap.map_smul_of_tower b.repr.toLinearMap a v
  exact DFunLike.congr_fun h i

omit [IsMulCommutative (R p T A)] in
theorem repr_self_eq_one (i j : Fin 2) :
    b.repr (b j) i = (1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j := by
  rw [Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

omit [IsMulCommutative (R p T A)] in

theorem exists_pow_smul_basis_eq :
    ∃ k : ℕ, ∀ j : Fin 2, ∃ y : T, ((p : ℚ_[p]) ^ k) • b j = toV p T y := by
  obtain ⟨k₀, y₀, h₀⟩ := exists_pow_smul_eq_toV (p := p) (b 0)
  obtain ⟨k₁, y₁, h₁⟩ := exists_pow_smul_eq_toV (p := p) (b 1)
  refine ⟨k₀ + k₁, fun j => ?_⟩
  fin_cases j
  · refine ⟨((p : ℤ_[p]) ^ k₁) • y₀, ?_⟩
    show ((p : ℚ_[p]) ^ (k₀ + k₁)) • b 0 = _
    rw [toV_smul, ← h₀, smul_smul, pow_add, mul_comm]
    simp
  · refine ⟨((p : ℤ_[p]) ^ k₀) • y₁, ?_⟩
    show ((p : ℚ_[p]) ^ (k₀ + k₁)) • b 1 = _
    rw [toV_smul, ← h₁, smul_smul, pow_add]
    simp

variable (op : ι₀ → 𝕋)

omit [IsMulCommutative (R p T A)] in

theorem exists_uniform_coord [Module.Finite ℤ_[p] T] (hop : ∀ (g : ι₀) (x : T), op g • x = A g x) :
    ∃ C₁ : ℕ, ∀ (x : T) (i : Fin 2),
      Θ p T 𝕋 C₁ 0 ((b.repr (toV p T x) i : R p T A) : Module.End ℚ_[p] (V p T)) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := T)

  have hpt : ∀ (x : T) (i : Fin 2), ∃ c : ℕ,
      Θ p T 𝕋 c 0 ((b.repr (toV p T x) i : R p T A) : Module.End ℚ_[p] (V p T)) := by
    intro x i
    obtain ⟨c, t, ht⟩ := exists_pow_smul_eq_ψ A op hop (b.repr (toV p T x) i).2
    exact ⟨c, t, by rw [ht, pow_zero, one_smul]⟩
  choose c hc using hpt
  refine ⟨s.sup fun x => c x 0 + c x 1, ?_⟩
  set C₁ := s.sup fun x => c x 0 + c x 1 with hC₁
  have hle : ∀ x ∈ s, ∀ i : Fin 2, c x i ≤ C₁ := by
    intro x hx i
    have h1 : c x 0 + c x 1 ≤ C₁ := Finset.le_sup (f := fun x => c x 0 + c x 1) hx
    fin_cases i
    · exact le_trans (Nat.le_add_right _ _) h1
    · exact le_trans (Nat.le_add_left _ _) h1
  intro x
  have hx : x ∈ Submodule.span ℤ_[p] (s : Set T) := by rw [hs]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact fun i => (hc x i).of_le (hle x hx i)
  | zero =>
    intro i
    rw [map_zero, map_zero, Finsupp.zero_apply, ZeroMemClass.coe_zero]
    exact Θ.zero _ _
  | add x y _ _ hx hy =>
    intro i
    rw [map_add, map_add, Finsupp.add_apply, AddMemClass.coe_add]
    exact (hx i).add (hy i)
  | smul a x _ hx =>
    intro i
    obtain ⟨t, ht⟩ := hx i
    refine ⟨a • t, ?_⟩
    rw [toV_smul, repr_smul_apply, coe_smul_R, smul_comm, ht, pow_zero, one_smul, one_smul, map_smul]
    exact algebraMap_smul ℚ_[p] a _

theorem Θ_Mat {k C₁ : ℕ} (hk : ∀ j : Fin 2, ∃ y : T, ((p : ℚ_[p]) ^ k) • b j = toV p T y)
    (hC₁ : ∀ (x : T) (i : Fin 2),
      Θ p T 𝕋 C₁ 0 ((b.repr (toV p T x) i : R p T A) : Module.End ℚ_[p] (V p T)))
    (τ : G) (i j : Fin 2) :
    Θ p T 𝕋 (k + C₁) 0 ((Mat (hcomm := hcomm) b τ i j : R p T A) : Module.End ℚ_[p] (V p T)) := by
  obtain ⟨y, hy⟩ := hk j
  obtain ⟨t, ht⟩ := hC₁ (ρ τ y) i
  refine ⟨t, ?_⟩
  rw [pow_add, mul_comm, mul_smul, ← coe_smul_R, Mat_apply, ← repr_smul_apply, ← LinearMap.map_smul,
    hy, ρV, bc_toV]
  exact ht

theorem Θ_Mat_sub_one {k C₁ : ℕ} (hk : ∀ j : Fin 2, ∃ y : T, ((p : ℚ_[p]) ^ k) • b j = toV p T y)
    (hC₁ : ∀ (x : T) (i : Fin 2),
      Θ p T 𝕋 C₁ 0 ((b.repr (toV p T x) i : R p T A) : Module.End ℚ_[p] (V p T)))
    {m' : ℕ} {σ : G} (hσ : ∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ m') • y) (i j : Fin 2) :
    Θ p T 𝕋 (k + C₁) m'
      ((Mat (hcomm := hcomm) b σ i j - (1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j : R p T A) :
        Module.End ℚ_[p] (V p T)) := by
  obtain ⟨y, hy⟩ := hk j
  obtain ⟨z, hz⟩ := hσ y
  obtain ⟨t, ht⟩ := hC₁ z i
  refine ⟨t, ?_⟩
  rw [pow_zero, one_smul] at ht

  have e1 : ((p : ℚ_[p]) ^ k) • ρV ρ σ (b j) = ((p : ℚ_[p]) ^ k) • b j + ((p : ℚ_[p]) ^ m') • toV p T z := by
    rw [← LinearMap.map_smul, hy, ρV, bc_toV, hz, map_add, toV_smul]
    simp

  have e2 : ((p : ℚ_[p]) ^ k) • Mat (hcomm := hcomm) b σ i j
      = ((p : ℚ_[p]) ^ k) • (1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j
        + ((p : ℚ_[p]) ^ m') • b.repr (toV p T z) i := by
    rw [Mat_apply, ← repr_smul_apply, e1, map_add, Finsupp.add_apply, repr_smul_apply, repr_smul_apply,
      repr_self_eq_one]
  have e3 := congrArg Subtype.val e2
  simp only [Subalgebra.coe_add, coe_smul_R] at e3
  show ((p : ℚ_[p]) ^ (k + C₁)) • ((Mat (hcomm := hcomm) b σ i j : Module.End ℚ_[p] (V p T))
      - ((1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j : Module.End ℚ_[p] (V p T))) = _
  rw [pow_add, mul_comm, mul_smul, smul_sub, e3, add_sub_cancel_left, smul_comm, ht, pow_smul_ψ]

end Level

end TrDetPkg

namespace TrDetPkg

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T]
variable {ι₀ : Type} {A : ι₀ → Module.End ℤ_[p] T}
variable {G : Type} [Group G] {ρ : G →* Module.End ℤ_[p] T}
variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]

section Level2

theorem trace_mul_sub_trace_fin_two {C : Type} [CommRing C] (N P : Matrix (Fin 2) (Fin 2) C)
    (n : Fin 2 → Fin 2 → C) (hn : ∀ i j, N i j = n i j + (1 : Matrix (Fin 2) (Fin 2) C) i j) :
    (N * P).trace - P.trace = n 0 0 * P 0 0 + n 0 1 * P 1 0 + n 1 0 * P 0 1 + n 1 1 * P 1 1 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, hn, hn, hn, hn, Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_ne h01,
    Matrix.one_apply_ne h01.symm]
  ring

theorem det_mul_sub_det_fin_two {C : Type} [CommRing C] (N P : Matrix (Fin 2) (Fin 2) C)
    (n : Fin 2 → Fin 2 → C) (hn : ∀ i j, N i j = n i j + (1 : Matrix (Fin 2) (Fin 2) C) i j) :
    (N * P).det - P.det
      = (n 0 0 + n 1 1 + n 0 0 * n 1 1 - n 0 1 * n 1 0) * (P 0 0 * P 1 1 - P 0 1 * P 1 0) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rw [Matrix.det_mul, Matrix.det_fin_two, Matrix.det_fin_two, hn, hn, hn, hn, Matrix.one_apply_eq,
    Matrix.one_apply_eq, Matrix.one_apply_ne h01, Matrix.one_apply_ne h01.symm]
  ring

open scoped IsMulCommutative

variable [IsMulCommutative (R p T A)] (b : Module.Basis (Fin 2) (R p T A) (V p T))
variable {hcomm : ∀ (σ : G) (g : ι₀) (x : T), ρ σ (A g x) = A g (ρ σ x)}

variable (op : ι₀ → 𝕋)

noncomputable def kExp : ℕ := (exists_pow_smul_basis_eq (p := p) b).choose

omit [IsMulCommutative (R p T A)] in
theorem kExp_spec : ∀ j : Fin 2, ∃ y : T, ((p : ℚ_[p]) ^ kExp b) • b j = toV p T y :=
  (exists_pow_smul_basis_eq (p := p) b).choose_spec

noncomputable def cExp [Module.Finite ℤ_[p] T] (hop : ∀ (g : ι₀) (x : T), op g • x = A g x) : ℕ :=
  (exists_uniform_coord (𝕋 := 𝕋) b op hop).choose

omit [IsMulCommutative (R p T A)] in
theorem cExp_spec [Module.Finite ℤ_[p] T] (hop : ∀ (g : ι₀) (x : T), op g • x = A g x) :
    ∀ (x : T) (i : Fin 2), Θ p T 𝕋 (cExp b op hop) 0
      ((b.repr (toV p T x) i : R p T A) : Module.End ℚ_[p] (V p T)) :=
  (exists_uniform_coord (𝕋 := 𝕋) b op hop).choose_spec

noncomputable def N₀ [Module.Finite ℤ_[p] T] (hop : ∀ (g : ι₀) (x : T), op g • x = A g x) : ℕ :=
  (kExp b + cExp b op hop + (kExp b + cExp b op hop)) + (kExp b + cExp b op hop + (kExp b + cExp b op hop))

theorem finite_level_tr [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
    (hop : ∀ (g : ι₀) (x : T), op g • x = A g x) (m : ℕ) (σ : G)
    (hσ : ∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ (m + N₀ b op hop)) • y) (τ : G) :
    ∃ t : 𝕋, (tr (hcomm := hcomm) b (σ * τ) : Module.End ℚ_[p] (V p T))
        - (tr (hcomm := hcomm) b τ : Module.End ℚ_[p] (V p T))
        = ψ p T 𝕋 (((p : ℤ_[p]) ^ m) • t) := by
  have hk := kExp_spec (p := p) b
  have hC₁ := cExp_spec (𝕋 := 𝕋) b op hop
  set k := kExp b
  set C₁ := cExp b op hop
  set K := k + C₁ with hK
  let N : Fin 2 → Fin 2 → R p T A := fun i j =>
    Mat (hcomm := hcomm) b σ i j - (1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j
  have hn : ∀ i j, Mat (hcomm := hcomm) b σ i j = N i j + (1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j :=
    fun i j => (sub_add_cancel (Mat (hcomm := hcomm) b σ i j)
      ((1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j)).symm
  set P : Matrix (Fin 2) (Fin 2) (R p T A) := Mat (hcomm := hcomm) b τ with hP
  let cN : Fin 2 → Fin 2 → Module.End ℚ_[p] (V p T) := fun i j =>
    ((N i j : R p T A) : Module.End ℚ_[p] (V p T))
  let cP : Fin 2 → Fin 2 → Module.End ℚ_[p] (V p T) := fun i j =>
    ((P i j : R p T A) : Module.End ℚ_[p] (V p T))
  have hNΘ : ∀ i j, Θ p T 𝕋 K (m + (K + K + (K + K))) (cN i j) :=
    fun i j => Θ_Mat_sub_one b hk hC₁ hσ i j
  have hPΘ : ∀ i j, Θ p T 𝕋 K 0 (cP i j) := fun i j => Θ_Mat b hk hC₁ τ i j
  have e_tr : tr (hcomm := hcomm) b (σ * τ) - tr (hcomm := hcomm) b τ
      = N 0 0 * P 0 0 + N 0 1 * P 1 0 + N 1 0 * P 0 1 + N 1 1 * P 1 1 := by
    rw [tr, tr, Mat_mul]
    exact trace_mul_sub_trace_fin_two _ _ N hn
  have e : (tr (hcomm := hcomm) b (σ * τ) : Module.End ℚ_[p] (V p T))
      - (tr (hcomm := hcomm) b τ : Module.End ℚ_[p] (V p T))
      = cN 0 0 * cP 0 0 + cN 0 1 * cP 1 0 + cN 1 0 * cP 0 1 + cN 1 1 * cP 1 1 := by
    have h := congrArg Subtype.val e_tr
    simp only [AddSubgroupClass.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul] at h
    exact h
  have hΘ : Θ p T 𝕋 ((K + K) + (K + K)) (m + (K + K + (K + K)))
      ((tr (hcomm := hcomm) b (σ * τ) : Module.End ℚ_[p] (V p T))
        - (tr (hcomm := hcomm) b τ : Module.End ℚ_[p] (V p T))) := by
    rw [e]
    refine Θ.of_le (Nat.le_add_right _ _) ?_
    exact ((((hNΘ 0 0).mul (hPΘ 0 0)).add ((hNΘ 0 1).mul (hPΘ 1 0))).add
      ((hNΘ 1 0).mul (hPΘ 0 1))).add ((hNΘ 1 1).mul (hPΘ 1 1))
  exact hΘ.cancel

theorem finite_level_dt [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
    (hop : ∀ (g : ι₀) (x : T), op g • x = A g x) (m : ℕ) (σ : G)
    (hσ : ∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ (m + N₀ b op hop)) • y) (τ : G) :
    ∃ t : 𝕋, (dt (hcomm := hcomm) b (σ * τ) : Module.End ℚ_[p] (V p T))
        - (dt (hcomm := hcomm) b τ : Module.End ℚ_[p] (V p T))
        = ψ p T 𝕋 (((p : ℤ_[p]) ^ m) • t) := by
  have hk := kExp_spec (p := p) b
  have hC₁ := cExp_spec (𝕋 := 𝕋) b op hop
  set k := kExp b
  set C₁ := cExp b op hop
  set K := k + C₁ with hK
  let N : Fin 2 → Fin 2 → R p T A := fun i j =>
    Mat (hcomm := hcomm) b σ i j - (1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j
  have hn : ∀ i j, Mat (hcomm := hcomm) b σ i j = N i j + (1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j :=
    fun i j => (sub_add_cancel (Mat (hcomm := hcomm) b σ i j)
      ((1 : Matrix (Fin 2) (Fin 2) (R p T A)) i j)).symm
  set P : Matrix (Fin 2) (Fin 2) (R p T A) := Mat (hcomm := hcomm) b τ with hP
  let cN : Fin 2 → Fin 2 → Module.End ℚ_[p] (V p T) := fun i j =>
    ((N i j : R p T A) : Module.End ℚ_[p] (V p T))
  let cP : Fin 2 → Fin 2 → Module.End ℚ_[p] (V p T) := fun i j =>
    ((P i j : R p T A) : Module.End ℚ_[p] (V p T))
  have hNΘ : ∀ i j, Θ p T 𝕋 K (m + (K + K + (K + K))) (cN i j) :=
    fun i j => Θ_Mat_sub_one b hk hC₁ hσ i j
  have hPΘ : ∀ i j, Θ p T 𝕋 K 0 (cP i j) := fun i j => Θ_Mat b hk hC₁ τ i j
  have e_dt : dt (hcomm := hcomm) b (σ * τ) - dt (hcomm := hcomm) b τ
      = (N 0 0 + N 1 1 + N 0 0 * N 1 1 - N 0 1 * N 1 0) * (P 0 0 * P 1 1 - P 0 1 * P 1 0) := by
    rw [dt, dt, Mat_mul]
    exact det_mul_sub_det_fin_two _ _ N hn
  have e : (dt (hcomm := hcomm) b (σ * τ) : Module.End ℚ_[p] (V p T))
      - (dt (hcomm := hcomm) b τ : Module.End ℚ_[p] (V p T))
      = (cN 0 0 + cN 1 1 + cN 0 0 * cN 1 1 - cN 0 1 * cN 1 0)
        * (cP 0 0 * cP 1 1 - cP 0 1 * cP 1 0) := by
    have h := congrArg Subtype.val e_dt
    simp only [AddSubgroupClass.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul] at h
    exact h
  have h1 : Θ p T 𝕋 (K + K) (m + (K + K + (K + K)))
      (cN 0 0 + cN 1 1 + cN 0 0 * cN 1 1 - cN 0 1 * cN 1 0) := by
    refine ((((hNΘ 0 0).of_le (Nat.le_add_right _ _)).add
      ((hNΘ 1 1).of_le (Nat.le_add_right _ _))).add ?_).sub ?_
    · exact ((hNΘ 0 0).mul (hNΘ 1 1)).of_ge (Nat.le_add_right _ _)
    · exact ((hNΘ 0 1).mul (hNΘ 1 0)).of_ge (Nat.le_add_right _ _)
  have h2 : Θ p T 𝕋 (K + K) 0 (cP 0 0 * cP 1 1 - cP 0 1 * cP 1 0) :=
    ((hPΘ 0 0).mul (hPΘ 1 1)).sub ((hPΘ 0 1).mul (hPΘ 1 0))
  have hΘ : Θ p T 𝕋 ((K + K) + (K + K)) (m + (K + K + (K + K)))
      ((dt (hcomm := hcomm) b (σ * τ) : Module.End ℚ_[p] (V p T))
        - (dt (hcomm := hcomm) b τ : Module.End ℚ_[p] (V p T))) := by
    rw [e]
    have h3 := h1.mul h2
    rw [Nat.add_zero] at h3
    exact h3
  exact hΘ.cancel

end Level2

end TrDetPkg

namespace TrDetPkg

section Final

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
variable {M : ℕ} [NeZero M] {S : Finset ℕ}
variable (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] T)
variable (A : CohCarrier.Gen M (↑S : Set ℕ) → Module.End ℤ_[p] T)
variable (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CohCarrier.Gen M (↑S : Set ℕ))
  (x : T), ρ σ (A g x) = A g (ρ σ x))
variable (hbij : ∀ u : (ZMod M)ˣ, Function.Bijective (A (CohCarrier.Gen.dia u)))
variable (hlevel : ∀ j : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
      ∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ j) • y)
variable (b : Module.Basis (Fin 2) (R p T A) (V p T))
variable (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
    ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ → ∀ x : T,
        A (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
            (ρ σ (ρ σ x))
          - A (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) (ρ σ x) + ℓ • x = 0)
variable (hdet : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
    ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
        (A (CohCarrier.Gen.dia
            (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange ℚ_[p] *
          (↑((b.repr ((ρ σ).baseChange ℚ_[p] (b 0))) 0 * (b.repr ((ρ σ).baseChange ℚ_[p] (b 1))) 1 -
              (b.repr ((ρ σ).baseChange ℚ_[p] (b 1))) 0 * (b.repr ((ρ σ).baseChange ℚ_[p] (b 0))) 1) :
            Module.End ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)) =
          (ℓ : Module.End ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)))
variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]
variable (op : CohCarrier.Gen M (↑S : Set ℕ) → 𝕋)
  (hop : ∀ (g : CohCarrier.Gen M (↑S : Set ℕ)) (x : T), op g • x = A g x)

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

local instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ _

omit [Fact p.Prime] in

theorem apply_eq_of_mem_ker (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ E]
    {h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hh : h ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) E).ker)
    (x : AlgebraicClosure ℚ) (hx : x ∈ E) : h x = x := by
  have h1 := AlgEquiv.restrictNormal_commutes h E ⟨x, hx⟩
  rw [MonoidHom.mem_ker] at hh
  have h2 : h.restrictNormal E = 1 := hh
  rw [h2, AlgEquiv.one_apply] at h1
  exact h1.symm

include hop

omit [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T] [NeZero M] in

theorem instComm : IsMulCommutative (R p T A) := isMulCommutative_R _ op hop

noncomputable def trJ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : R p T A :=
  haveI := instComm A op hop
  tr (ρ := ρ) (hcomm := hcomm) b σ

noncomputable def dtJ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : R p T A :=
  haveI := instComm A op hop
  dt (ρ := ρ) (hcomm := hcomm) b σ

omit [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T] [NeZero M] in
include hdet in
open scoped IsMulCommutative in

theorem frob_dt {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p)
    (A' : ValuationSubring (AlgebraicClosure ℚ)) (hA : A'.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A'.IsFrobeniusAt σ ℓ) :
    ψ p T 𝕋 (op (CohCarrier.Gen.dia
        (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))))
      * (dtJ ρ A hcomm b op hop σ : Module.End ℚ_[p] (V p T))
      = (ℓ : Module.End ℚ_[p] (V p T)) := by
  haveI := instComm A op hop
  have h := hdet ℓ hℓ hℓS hℓM hℓp A' hA σ hσ
  rw [ψ_op A op hop, bc_apply]
  have e : dtJ ρ A hcomm b op hop σ
      = b.repr (ρV ρ σ (b 0)) 0 * b.repr (ρV ρ σ (b 1)) 1
        - b.repr (ρV ρ σ (b 1)) 0 * b.repr (ρV ρ σ (b 0)) 1 := by
    rw [dtJ, dt, Matrix.det_fin_two, Mat_apply, Mat_apply, Mat_apply, Mat_apply]
  rw [e, ρV, bc_apply]
  exact h

omit [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T] [NeZero M] in
include hES hdet in

theorem frob_tr {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p)
    (A' : ValuationSubring (AlgebraicClosure ℚ)) (hA : A'.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A'.IsFrobeniusAt σ ℓ) :
    ψ p T 𝕋 (op (CohCarrier.Gen.dia
        (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))))
      * (trJ ρ A hcomm b op hop σ : Module.End ℚ_[p] (V p T))
      = ψ p T 𝕋 (op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) := by
  haveI := instComm A op hop
  have hES' : ∀ x : T,
      op (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
          • ρ σ (ρ σ x)
        - op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) • ρ σ x + ℓ • x = 0 := fun x => by
    rw [hop, hop]
    exact hES ℓ hℓ hℓS hℓM hℓp A' hA σ hσ x
  exact ψ_mul_tr_eq (hcomm := hcomm) b σ _ _ ℓ hES' (frob_dt ρ A hcomm b hdet op hop hℓ hℓS hℓM hℓp A' hA σ hσ)

omit [NeZero M] in
include hbij in

theorem unit_dia (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0) (u : (ZMod M)ˣ) :
    ∃ E : 𝕋, op (CohCarrier.Gen.dia u) * E = 1 := by
  refine exists_mul_eq_one_of_bijective (p := p) hfaith _ ?_
  have : (fun x : T => op (CohCarrier.Gen.dia u) • x) = ⇑(A (CohCarrier.Gen.dia u)) :=
    funext fun x => hop _ x
  rw [this]
  exact hbij u

omit hop in

noncomputable def Lf (j : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) := (hlevel j).choose

omit [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T] hop in
theorem Lf_fin (j : ℕ) : FiniteDimensional ℚ (Lf ρ hlevel j) := (hlevel j).choose_spec.1

omit [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T] hop in
theorem Lf_fix (j : ℕ) : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    (∀ x ∈ Lf ρ hlevel j, σ x = x) → ∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ j) • y :=
  (hlevel j).choose_spec.2

noncomputable def N0 : ℕ :=
  haveI := instComm A op hop
  N₀ b op hop

omit [NeZero M] in

theorem level_trJ (m : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ (m + N0 A b op hop)) • y)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ t : 𝕋, (trJ ρ A hcomm b op hop (σ * τ) : Module.End ℚ_[p] (V p T))
        - (trJ ρ A hcomm b op hop τ : Module.End ℚ_[p] (V p T))
        = ψ p T 𝕋 (((p : ℤ_[p]) ^ m) • t) := by
  haveI := instComm A op hop
  exact finite_level_tr (hcomm := hcomm) b op hop m σ hσ τ

omit [NeZero M] in

theorem level_dtJ (m : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ (m + N0 A b op hop)) • y)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ t : 𝕋, (dtJ ρ A hcomm b op hop (σ * τ) : Module.End ℚ_[p] (V p T))
        - (dtJ ρ A hcomm b op hop τ : Module.End ℚ_[p] (V p T))
        = ψ p T 𝕋 (((p : ℤ_[p]) ^ m) • t) := by
  haveI := instComm A op hop
  exact finite_level_dt (hcomm := hcomm) b op hop m σ hσ τ

omit [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T] [NeZero M] in
theorem trJ_conj (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    trJ ρ A hcomm b op hop (σ * τ * σ⁻¹) = trJ ρ A hcomm b op hop τ := by
  haveI := instComm A op hop
  exact tr_conj (hcomm := hcomm) b σ τ

omit [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T] [NeZero M] in
theorem dtJ_conj (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    dtJ ρ A hcomm b op hop (σ * τ * σ⁻¹) = dtJ ρ A hcomm b op hop τ := by
  haveI := instComm A op hop
  exact dt_conj (hcomm := hcomm) b σ τ

omit [Module.Free ℤ_[p] T] in
include hlevel in

theorem exists_frob_conj (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ (ℓ : ℕ) (A' : ValuationSubring (AlgebraicClosure ℚ)) (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (_ : ℓ.Prime), ℓ ∉ (↑S : Set ℕ) ∧ ¬ ℓ ∣ M ∧ ℓ ≠ p ∧ A'.LiesOverPrime ℓ ∧ A'.IsFrobeniusAt τ ℓ ∧
      ∀ x : T, ∃ y : T,
        ρ (g * τ * g⁻¹ * σ⁻¹) x = x + ((p : ℤ_[p]) ^ (0 + N0 A b op hop)) • y := by
  let L0 := Lf ρ hlevel (0 + N0 A b op hop)
  haveI : FiniteDimensional ℚ L0 := Lf_fin ρ hlevel _
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ L0 (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ E := IsGalois.normalClosure ℚ L0 (AlgebraicClosure ℚ)
  haveI : NumberField E := NumberField.mk
  obtain ⟨ℓ, Apl, τ, g, hℓ, hℓS', hApl, hτ, hmem⟩ :=
    FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker E
      (H := (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) E).ker) le_rfl
      (S ∪ M.primeFactors ∪ {p}) σ
  have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h' =>
    hℓS' (Finset.mem_union_left _ (Finset.mem_union_left _ h'))
  have hℓM : ¬ ℓ ∣ M := fun h' =>
    hℓS' (Finset.mem_union_left _ (Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨hℓ, h', NeZero.ne M⟩)))
  have hℓp : ℓ ≠ p := fun h' =>
    hℓS' (Finset.mem_union_right _ (Finset.mem_singleton.mpr h'))
  have hfixL : ∀ x ∈ L0, (g * τ * g⁻¹ * σ⁻¹) x = x := fun x hx =>
    apply_eq_of_mem_ker E hmem x (IntermediateField.le_normalClosure L0 hx)
  exact ⟨ℓ, Apl, τ, g, hℓ, hℓS, hℓM, hℓp, hApl, hτ, Lf_fix ρ hlevel _ _ hfixL⟩

include hbij hlevel hES hdet in

theorem val_trJ (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ t : 𝕋, (trJ ρ A hcomm b op hop σ : Module.End ℚ_[p] (V p T)) = ψ p T 𝕋 t := by
  obtain ⟨ℓ, A', τ, g, hℓ, hℓS, hℓM, hℓp, hA, hτ, hh⟩ := exists_frob_conj ρ A hlevel b op hop σ
  obtain ⟨t, ht⟩ := level_trJ ρ A hcomm b op hop 0 _ hh σ
  have hhσ : g * τ * g⁻¹ * σ⁻¹ * σ = g * τ * g⁻¹ := inv_mul_cancel_right _ _
  rw [hhσ, trJ_conj] at ht
  have htr := frob_tr ρ A hcomm b hES hdet op hop hℓ hℓS hℓM hℓp A' hA τ hτ
  obtain ⟨E', hE'⟩ := unit_dia A hbij op hop hfaith
    (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))
  have htrτ : (trJ ρ A hcomm b op hop τ : Module.End ℚ_[p] (V p T))
      = ψ p T 𝕋 (E' * op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) := by
    have := congrArg (ψ p T 𝕋 E' * ·) htr
    rwa [← mul_assoc, ← map_mul, mul_comm E', hE', map_one, one_mul, ← map_mul] at this
  refine ⟨E' * op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) - ((p : ℤ_[p]) ^ 0) • t, ?_⟩
  rw [map_sub, ← htrτ, ← ht, sub_sub_cancel]

include hbij hlevel hdet in

theorem val_dtJ (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ d : 𝕋, (dtJ ρ A hcomm b op hop σ : Module.End ℚ_[p] (V p T)) = ψ p T 𝕋 d := by
  obtain ⟨ℓ, A', τ, g, hℓ, hℓS, hℓM, hℓp, hA, hτ, hh⟩ := exists_frob_conj ρ A hlevel b op hop σ
  obtain ⟨d, hd⟩ := level_dtJ ρ A hcomm b op hop 0 _ hh σ
  have hhσ : g * τ * g⁻¹ * σ⁻¹ * σ = g * τ * g⁻¹ := inv_mul_cancel_right _ _
  rw [hhσ, dtJ_conj] at hd
  have hdt' := frob_dt ρ A hcomm b hdet op hop hℓ hℓS hℓM hℓp A' hA τ hτ
  obtain ⟨E', hE'⟩ := unit_dia A hbij op hop hfaith
    (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))
  have hdtτ : (dtJ ρ A hcomm b op hop τ : Module.End ℚ_[p] (V p T)) = ψ p T 𝕋 (E' * ℓ) := by
    have := congrArg (ψ p T 𝕋 E' * ·) hdt'
    rwa [← mul_assoc, ← map_mul, mul_comm E', hE', map_one, one_mul,
      ← map_natCast (ψ p T 𝕋), ← map_mul] at this
  refine ⟨E' * ℓ - ((p : ℤ_[p]) ^ 0) • d, ?_⟩
  rw [map_sub, ← hdtτ, ← hd, sub_sub_cancel]

omit [Module.Finite ℤ_[p] T] [NeZero M] in
include hcomm in

theorem rho_smul (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : 𝕋) (x : T) :
    ρ σ (t • x) = t • ρ σ x := by
  apply toV_injective (p := p)
  have e1 : toV p T (ρ σ (t • x)) = (ρV ρ σ * ψ p T 𝕋 t) (toV p T x) := rfl
  have e2 : toV p T (t • ρ σ x) = (ψ p T 𝕋 t * ρV ρ σ) (toV p T x) := rfl
  rw [e1, e2, commute_ρV A ρ hcomm σ (ψ_mem_R A op hop hgen t)]

end Final

end TrDetPkg

namespace TrDetPkg

section Final2

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
variable {M : ℕ} [NeZero M] {S : Finset ℕ}
variable (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] T)
variable (A : CohCarrier.Gen M (↑S : Set ℕ) → Module.End ℤ_[p] T)
variable (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CohCarrier.Gen M (↑S : Set ℕ))
  (x : T), ρ σ (A g x) = A g (ρ σ x))
variable (hbij : ∀ u : (ZMod M)ˣ, Function.Bijective (A (CohCarrier.Gen.dia u)))
variable (hlevel : ∀ j : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
      ∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ j) • y)
variable (b : Module.Basis (Fin 2) (R p T A) (V p T))
variable (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
    ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ → ∀ x : T,
        A (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
            (ρ σ (ρ σ x))
          - A (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) (ρ σ x) + ℓ • x = 0)
variable (hdet : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
    ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
        (A (CohCarrier.Gen.dia
            (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange ℚ_[p] *
          (↑((b.repr ((ρ σ).baseChange ℚ_[p] (b 0))) 0 * (b.repr ((ρ σ).baseChange ℚ_[p] (b 1))) 1 -
              (b.repr ((ρ σ).baseChange ℚ_[p] (b 1))) 0 * (b.repr ((ρ σ).baseChange ℚ_[p] (b 0))) 1) :
            Module.End ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)) =
          (ℓ : Module.End ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)))
variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]
variable (op : CohCarrier.Gen M (↑S : Set ℕ) → 𝕋)
  (hop : ∀ (g : CohCarrier.Gen M (↑S : Set ℕ)) (x : T), op g • x = A g x)

omit [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T] [NeZero M] in
include hop in

theorem lsmul_baseChange_eq_trace (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : 𝕋)
    (ht : (trJ ρ A hcomm b op hop σ : Module.End ℚ_[p] (V p T)) = ψ p T 𝕋 t) :
    (Algebra.lsmul ℤ_[p] ℤ_[p] T t).baseChange ℚ_[p]
      = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 + b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1) := by
  haveI := instComm A op hop
  have e : trJ ρ A hcomm b op hop σ = b.repr (ρV ρ σ (b 0)) 0 + b.repr (ρV ρ σ (b 1)) 1 := by
    rw [trJ, tr, Matrix.trace_fin_two, Mat_apply, Mat_apply]
  have h : ψ p T 𝕋 t = ↑(b.repr (ρV ρ σ (b 0)) 0 + b.repr (ρV ρ σ (b 1)) 1) := by rw [← e]; exact ht.symm
  exact h

omit [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T] [NeZero M] in
include hop in
open scoped IsMulCommutative in

theorem lsmul_baseChange_eq_det (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (d : 𝕋)
    (hd : (dtJ ρ A hcomm b op hop σ : Module.End ℚ_[p] (V p T)) = ψ p T 𝕋 d) :
    (Algebra.lsmul ℤ_[p] ℤ_[p] T d).baseChange ℚ_[p]
      = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1
          - b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 1) := by
  haveI := instComm A op hop
  have e : dtJ ρ A hcomm b op hop σ = b.repr (ρV ρ σ (b 0)) 0 * b.repr (ρV ρ σ (b 1)) 1
      - b.repr (ρV ρ σ (b 1)) 0 * b.repr (ρV ρ σ (b 0)) 1 := by
    rw [dtJ, dt, Matrix.det_fin_two, Mat_apply, Mat_apply, Mat_apply, Mat_apply]
  have h : ψ p T 𝕋 d = ↑(b.repr (ρV ρ σ (b 0)) 0 * b.repr (ρV ρ σ (b 1)) 1
      - b.repr (ρV ρ σ (b 1)) 0 * b.repr (ρV ρ σ (b 0)) 1) := by rw [← e]; exact hd.symm
  exact h

include hcomm hbij hlevel hES hdet hop

open scoped IsMulCommutative in

theorem main𝕋 (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤) :
    ∃ (tt dd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → 𝕋)
      (L : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)),
      tt 1 = 2 ∧ dd 1 = 1 ∧
      (∀ σ τ, tt (σ * τ * σ⁻¹) = tt τ) ∧ (∀ σ τ, dd (σ * τ * σ⁻¹) = dd τ) ∧
      (∀ σ τ, dd (σ * τ) = dd σ * dd τ) ∧
      (∀ σ, tt σ * tt σ = tt (σ * σ) + 2 * dd σ) ∧
      (∀ σ (x : T), ρ σ (ρ σ x) - tt σ • ρ σ x + dd σ • x = 0) ∧
      (∀ σ (t : 𝕋) (x : T), ρ σ (t • x) = t • ρ σ x) ∧
      (∀ n : ℕ, FiniteDimensional ℚ (L n) ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L n, σ x = x) →
          (∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ n) • y) ∧
          (∀ τ, ∃ c : 𝕋, tt (σ * τ) = tt τ + (p : 𝕋) ^ n * c) ∧
          (∀ τ, ∃ c : 𝕋, dd (σ * τ) = dd τ + (p : 𝕋) ^ n * c)) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
            op (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
                * tt σ = op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ∧
            op (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
                * dd σ = (ℓ : 𝕋)) ∧
      (∀ σ, (Algebra.lsmul ℤ_[p] ℤ_[p] T (tt σ)).baseChange ℚ_[p]
            = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 + b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1) ∧
          (Algebra.lsmul ℤ_[p] ℤ_[p] T (dd σ)).baseChange ℚ_[p]
            = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1
                - b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 1)) := by
  haveI := instComm A op hop
  have hψinj : Function.Injective (ψ p T 𝕋) := ψ_injective hfaith
  choose tt htt using val_trJ ρ A hcomm hbij hlevel b hES hdet op hop hfaith
  choose dd hdd using val_dtJ ρ A hcomm hbij hlevel b hdet op hop hfaith
  refine ⟨tt, dd, fun n => Lf ρ hlevel (n + N0 A b op hop), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rho_smul ρ A hcomm op hop hgen, ?_, ?_, ?_⟩
  ·
    apply hψinj
    rw [← htt, trJ, tr_one, map_ofNat]
    rfl
  ·
    apply hψinj
    rw [← hdd, dtJ, dt_one, map_one]
    rfl
  · intro σ τ
    apply hψinj
    rw [← htt, ← htt, trJ_conj]
  · intro σ τ
    apply hψinj
    rw [← hdd, ← hdd, dtJ_conj]
  · intro σ τ
    apply hψinj
    rw [map_mul, ← hdd, ← hdd, ← hdd, dtJ, dtJ, dtJ, dt_mul]
    rfl
  · intro σ
    apply hψinj
    have e := congrArg Subtype.val (tr_mul_self (ρ := ρ) (hcomm := hcomm) b σ)
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add] at e
    rw [map_add, map_mul, map_mul, ← htt, ← htt, ← hdd, map_ofNat, trJ, trJ, dtJ]
    exact e
  · intro σ x
    exact cayleyHamilton_T (hcomm := hcomm) b σ (tt σ) (dd σ) (htt σ) (hdd σ) x
  · intro n
    refine ⟨Lf_fin ρ hlevel _, fun σ hσ => ⟨?_, ?_, ?_⟩⟩
    · intro x
      obtain ⟨y, hy⟩ := Lf_fix ρ hlevel (n + N0 A b op hop) σ hσ x
      exact ⟨((p : ℤ_[p]) ^ N0 A b op hop) • y, by rw [hy, smul_smul, ← pow_add]⟩
    · intro τ
      obtain ⟨t, ht⟩ := level_trJ ρ A hcomm b op hop n σ (Lf_fix ρ hlevel _ σ hσ) τ
      refine ⟨t, hψinj ?_⟩
      rw [map_add, ← htt, ← htt, map_mul, map_pow, map_natCast, ← sub_eq_iff_eq_add', ht, map_smul,
        Algebra.smul_def, map_pow, map_natCast]
    · intro τ
      obtain ⟨t, ht⟩ := level_dtJ ρ A hcomm b op hop n σ (Lf_fix ρ hlevel _ σ hσ) τ
      refine ⟨t, hψinj ?_⟩
      rw [map_add, ← hdd, ← hdd, map_mul, map_pow, map_natCast, ← sub_eq_iff_eq_add', ht, map_smul,
        Algebra.smul_def, map_pow, map_natCast]
  · intro ℓ hℓ hℓS hℓM hℓp A' hA σ hσ
    constructor
    · apply hψinj
      rw [map_mul, ← htt]
      exact frob_tr ρ A hcomm b hES hdet op hop hℓ hℓS hℓM hℓp A' hA σ hσ
    · apply hψinj
      rw [map_mul, ← hdd, map_natCast]
      exact frob_dt ρ A hcomm b hdet op hop hℓ hℓS hℓM hℓp A' hA σ hσ
  ·
    intro σ
    constructor
    · exact lsmul_baseChange_eq_trace ρ A hcomm b op hop σ (tt σ) (htt σ)
    · exact lsmul_baseChange_eq_det ρ A hcomm b op hop σ (dd σ) (hdd σ)

end Final2

end TrDetPkg

open scoped TensorProduct in

theorem solution
    (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] (M : ℕ) [NeZero M] (S : Finset ℕ)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] T)
    (A : CohCarrier.Gen M (↑S : Set ℕ) → Module.End ℤ_[p] T)
    (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CohCarrier.Gen M (↑S : Set ℕ))
      (x : T), ρ σ (A g x) = A g (ρ σ x))
    (hbij : ∀ u : (ZMod M)ˣ, Function.Bijective (A (CohCarrier.Gen.dia u)))
    (hlevel : ∀ j : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ j) • y)
    (b : Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : CohCarrier.Gen M (↑S : Set ℕ) => (A g).baseChange ℚ_[p]))
      (ℚ_[p] ⊗[ℤ_[p]] T))
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
      ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ → ∀ x : T,
          A (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
              (ρ σ (ρ σ x))
            - A (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) (ρ σ x) + ℓ • x = 0)
    (hdet : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
      ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
          (A (CohCarrier.Gen.dia
              (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange ℚ_[p] *
            (↑((b.repr ((ρ σ).baseChange ℚ_[p] (b 0))) 0 * (b.repr ((ρ σ).baseChange ℚ_[p] (b 1))) 1 -
                (b.repr ((ρ σ).baseChange ℚ_[p] (b 1))) 0 * (b.repr ((ρ σ).baseChange ℚ_[p] (b 0))) 1) :
              Module.End ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)) =
            (ℓ : Module.End ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)))
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]
    (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0)
    (op : CohCarrier.Gen M (↑S : Set ℕ) → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M (↑S : Set ℕ)) (x : T), op g • x = A g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤) :
    ∃ (t d : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → 𝕋)
      (L : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)),

      t 1 = 2 ∧ d 1 = 1 ∧
      (∀ σ τ, t (σ * τ * σ⁻¹) = t τ) ∧ (∀ σ τ, d (σ * τ * σ⁻¹) = d τ) ∧
      (∀ σ τ, d (σ * τ) = d σ * d τ) ∧
      (∀ σ, t σ * t σ = t (σ * σ) + 2 * d σ) ∧
      (∀ σ (x : T), ρ σ (ρ σ x) - t σ • ρ σ x + d σ • x = 0) ∧
      (∀ σ (u : 𝕋) (x : T), ρ σ (u • x) = u • ρ σ x) ∧

      (∀ n : ℕ, FiniteDimensional ℚ (L n) ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L n, σ x = x) →
          (∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ n) • y) ∧
          (∀ τ, ∃ c : 𝕋, t (σ * τ) = t τ + (p : 𝕋) ^ n * c) ∧
          (∀ τ, ∃ c : 𝕋, d (σ * τ) = d τ + (p : 𝕋) ^ n * c)) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
            op (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
                * t σ = op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ∧
            op (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
                * d σ = (ℓ : 𝕋)) ∧

      (∀ σ, (Algebra.lsmul ℤ_[p] ℤ_[p] T (t σ)).baseChange ℚ_[p]
            = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 + b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1) ∧
          (Algebra.lsmul ℤ_[p] ℤ_[p] T (d σ)).baseChange ℚ_[p]
            = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1
                - b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 1)) :=
  TrDetPkg.main𝕋 ρ A hcomm hbij hlevel b hES hdet op hop hfaith hgen

end S_GaloisLattice_exists_trace_det_of_basis_fin_two_of_frobenius_relations
end P2MW
export P2MW.S_GaloisLattice_exists_trace_det_of_basis_fin_two_of_frobenius_relations (solution)
