-- Prove2me | solution 1 for GaloisLattice.exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4e17479b-7b86-538c-ac27-197f8fefd60b

import Mathlib
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_IharaLemma_nonempty_idempotentSplitting_of_finite
import Theorems.Thm_IharaLemma_IdempotentSplitting_finite_cornerRing
import Theorems.Thm_IharaLemma_IdempotentSplitting_exists_basis_cornerSubmodule_coe_eq_smul
import Theorems.Thm_IsLocalRing_free_and_finrank_add_eq_of_isCompl
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct

noncomputable section

namespace OrdLat

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

theorem commute_bc_of_mem_R (f : Module.End ℤ_[p] T) (hcomm : ∀ (g : ι₀) (x : T), f (A g x) = A g (f x))
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) : r * bc p T f = bc p T f * r := by
  have hle : R p T A ≤ Subalgebra.centralizer ℚ_[p] {bc p T f} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩ _ rfl
    show bc p T f * bc p T (A i) = bc p T (A i) * bc p T f
    rw [← map_mul, ← map_mul]
    congr 1
    exact LinearMap.ext fun x => hcomm i x
  exact (Subalgebra.mem_centralizer_iff ℚ_[p]).mp (hle hr) _ rfl |>.symm

end OrdLat

namespace OrdLat

section Invol

variable {C : Type} [CommRing C] {N : Type} [AddCommGroup N] [Module C N]

theorem isCompl_eigenspaces_of_involution (s : N →ₗ[C] N) (hs : ∀ x, s (s x) = x)
    (h2 : IsUnit (2 : C)) :
    IsCompl (LinearMap.ker (s + LinearMap.id)) (LinearMap.ker (s - LinearMap.id)) := by
  obtain ⟨u, hu⟩ := h2
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨h0, h1⟩ := Submodule.mem_inf.mp hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at h0
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h1
    rw [h1] at h0
    have h2x : (2 : C) • x = 0 := by rw [two_smul]; exact h0
    calc x = ((u⁻¹ : Cˣ) : C) • ((u : C) • x) := by rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hu, h2x, smul_zero]
  · rw [Submodule.eq_top_iff']
    intro x
    have hx : x = ((u⁻¹ : Cˣ) : C) • (x - s x) + ((u⁻¹ : Cˣ) : C) • (x + s x) := by
      rw [← smul_add, show x - s x + (x + s x) = (2 : C) • x by rw [two_smul]; abel, ← hu, smul_smul,
        Units.inv_mul, one_smul]
    rw [hx]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, LinearMap.map_smul, map_sub, hs,
        ← smul_add, show s x - x + (x - s x) = 0 by abel, smul_zero]
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.map_smul, map_add, hs,
        ← smul_sub, show s x + x - (x + s x) = 0 by abel, smul_zero]

end Invol

section RankParity

variable {K : Type} [Field K] {N : Type} [AddCommGroup N] [Module K N] [FiniteDimensional K N]

theorem finrank_eq_of_similitude (N0 N1 : Submodule K N) (hc : IsCompl N0 N1)
    (B : N →ₗ[K] N →ₗ[K] K) (hB : ∀ x, (∀ y, B x y = 0) → x = 0)
    (g : N →ₗ[K] N) (u : K) (hu : u * (u - 1) ≠ 0)
    (hg0 : ∀ x ∈ N0, g x = u • x) (hg1 : ∀ x, g x - x ∈ N0)
    (hsim : ∀ x y, B (g x) (g y) = u * B x y) :
    Module.finrank K N0 = Module.finrank K N1 := by

  have hiso : ∀ x ∈ N0, ∀ y ∈ N0, B x y = 0 := by
    intro x hx y hy
    have h := hsim x y
    rw [hg0 x hx, hg0 y hy] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    have h' : (u * (u - 1)) * B x y = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' hu
    · exact h''

  have hdec : ∀ y : N, ∃ y0 ∈ N0, ∃ y1 ∈ N1, y = y0 + y1 := by
    intro y
    have hy : y ∈ N0 ⊔ N1 := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y0, hy0, y1, hy1, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨y0, hy0, y1, hy1, rfl⟩

  let φ : N0 →ₗ[K] Module.Dual K N1 := (B.domRestrict N0).flip.domRestrict N1 |>.flip
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hx1 : ∀ y ∈ N1, B x y = 0 := fun y hy => by
      have := LinearMap.congr_fun hx ⟨y, hy⟩
      exact this
    have hall : ∀ y, B x y = 0 := by
      intro y
      obtain ⟨y0, hy0, y1, hy1, rfl⟩ := hdec y
      rw [map_add, hiso x x.2 y0 hy0, hx1 y1 hy1, add_zero]
    exact Subtype.ext (hB x hall)

  let χ : N1 →ₗ[K] Module.Dual K N0 := (B.domRestrict N1).flip.domRestrict N0 |>.flip
  have hχ : Function.Injective χ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hw0 : ∀ x ∈ N0, B w x = 0 := fun x hx => by
      have := LinearMap.congr_fun hw ⟨x, hx⟩
      exact this

    have hkey : ∀ y, B (g w - w - (u - 1) • (w : N)) y = 0 := by
      intro y
      have h := hsim w y
      have e1 : g w = (w : N) + (g w - w) := by abel
      have e2 : g y = y + (g y - y) := by abel
      rw [e1, e2] at h
      simp only [map_add, LinearMap.add_apply] at h
      rw [hw0 _ (hg1 y), hiso _ (hg1 w) _ (hg1 y), add_zero, add_zero] at h
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h ⊢
      linear_combination h
    have hmem : (u - 1) • (w : N) ∈ N0 := by
      have h0 : g w - w - (u - 1) • (w : N) = 0 := hB _ hkey
      rw [sub_eq_zero] at h0
      rw [← h0]
      exact hg1 w
    have hu1 : u - 1 ≠ 0 := fun h => hu (by rw [h, mul_zero])
    have hwN0 : (w : N) ∈ N0 := by
      have := N0.smul_mem (u - 1)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hu1, one_smul] at this
    have : (w : N) = 0 := by
      have hmem2 : (w : N) ∈ N0 ⊓ N1 := Submodule.mem_inf.mpr ⟨hwN0, w.2⟩
      rw [hc.inf_eq_bot] at hmem2
      exact (Submodule.mem_bot K).mp hmem2
    exact Subtype.ext this
  have h1 := LinearMap.finrank_le_finrank_of_injective hφ
  have h2 := LinearMap.finrank_le_finrank_of_injective hχ
  rw [Subspace.dual_finrank_eq] at h1 h2
  omega

end RankParity

end OrdLat

namespace OrdLat

section Core

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T]
variable {ι₀ : Type} {A : ι₀ → Module.End ℤ_[p] T}
variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]

scoped instance instCommRingR [h : IsMulCommutative (R p T A)] : CommRing (R p T A) :=
  { (inferInstance : Ring (R p T A)) with mul_comm := fun a b => h.is_comm.comm a b }

scoped instance instIsScalarTower_R_V : IsScalarTower ℚ_[p] (R p T A) (V p T) :=
  ⟨fun c r v => by
    show ((c • r : R p T A) : Module.End ℚ_[p] (V p T)) v = c • ((r : Module.End ℚ_[p] (V p T)) v)
    rfl⟩

theorem R_smul_def (r : R p T A) (v : V p T) : r • v = (r : Module.End ℚ_[p] (V p T)) v := rfl

variable (A) in

noncomputable def toRLin (f : Module.End ℤ_[p] T) (hf : ∀ (g : ι₀) (x : T), f (A g x) = A g (f x)) :
    V p T →ₗ[R p T A] V p T where
  toFun := bc p T f
  map_add' := map_add _
  map_smul' r v := by
    show bc p T f ((r : Module.End ℚ_[p] (V p T)) v) = (r : Module.End ℚ_[p] (V p T)) (bc p T f v)
    rw [← Module.End.mul_apply, ← commute_bc_of_mem_R A f hf r.2, Module.End.mul_apply]

theorem toRLin_apply (f : Module.End ℤ_[p] T) (hf : ∀ (g : ι₀) (x : T), f (A g x) = A g (f x))
    (v : V p T) : toRLin A f hf v = bc p T f v := rfl

theorem comm_A_of_comm_𝕋 {op : ι₀ → 𝕋} (hop : ∀ (g : ι₀) (x : T), op g • x = A g x)
    (f : Module.End ℤ_[p] T) (hf : ∀ (t : 𝕋) (x : T), f (t • x) = t • f x) :
    ∀ (g : ι₀) (x : T), f (A g x) = A g (f x) := by
  intro g x
  rw [← hop, ← hop, hf]

theorem selfAdjoint_of_mem_R [IsMulCommutative (R p T A)]
    (Bf : V p T →ₗ[ℚ_[p]] V p T →ₗ[ℚ_[p]] ℚ_[p])
    (hB : ∀ (g : ι₀) (x y : V p T), Bf (bc p T (A g) x) y = Bf x (bc p T (A g) y))
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) :
    ∀ x y : V p T, Bf (r x) y = Bf x (r y) := by
  induction hr using Algebra.adjoin_induction with
  | mem r hr =>
    obtain ⟨g, rfl⟩ := hr
    exact hB g
  | algebraMap c =>
    intro x y
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.one_apply, map_smul, map_smul, LinearMap.smul_apply]
  | add r s _ _ hr hs =>
    intro x y
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, map_add, LinearMap.add_apply, hr, hs]
  | mul r s hr' hs' hr hs =>
    intro x y
    have hcomm : r * s = s * r := by
      have := mul_comm (⟨r, hr'⟩ : R p T A) ⟨s, hs'⟩
      exact congrArg Subtype.val this
    rw [Module.End.mul_apply, hr, hs, hcomm, Module.End.mul_apply]

variable (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)

theorem mem_corner_iff (x : T) :
    x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀) ↔ S'.e i₀ • x = x := by
  constructor
  · rintro ⟨z, rfl⟩
    show S'.e i₀ • (S'.e i₀ • z) = S'.e i₀ • z
    rw [smul_smul, (S'.idem i₀).eq]
  · intro h
    exact ⟨x, h⟩

theorem toCornerRing_smul_of_mem (t : 𝕋) {x : T} (hx : x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀)) :
    ((S'.toCornerRing i₀ t : S'.CornerRing i₀) : 𝕋) • x = t • x := by
  have he := (mem_corner_iff S' i₀ x).mp hx
  show (S'.e i₀ * t * S'.e i₀) • x = t • x
  rw [mul_smul, mul_smul, he, ← mul_smul, mul_comm, mul_smul, he]

variable [Module.Free ℤ_[p] T]

theorem mem_corner_of_toV {v : V p T} (hv : ψ p T 𝕋 (S'.e i₀) v = v) {k : ℕ} {x : T}
    (hx : ((p : ℚ_[p]) ^ k) • v = toV p T x) :
    x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀) := by
  rw [mem_corner_iff]
  apply toV_injective (p := p)
  rw [← ψ_toV, ← hx, map_smul, hv]

theorem apply_eq_smul_of_toV (f : Module.End ℤ_[p] T) (c : ℤ_[p]) {v : V p T} (hv : bc p T f v = (c : ℚ_[p]) • v)
    {k : ℕ} {x : T} (hx : ((p : ℚ_[p]) ^ k) • v = toV p T x) : f x = c • x := by
  apply toV_injective (p := p)
  rw [← bc_toV, ← hx, map_smul, hv, toV_smul, smul_comm, hx]

theorem bc_toV_eq_smul (f : Module.End ℤ_[p] T) (c : ℤ_[p]) {x : T} (hx : f x = c • x) :
    bc p T f (toV p T x) = (c : ℚ_[p]) • toV p T x := by
  rw [bc_toV, hx, toV_smul]

end Core

end OrdLat
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"

namespace OrdLat
namespace Corner

open IharaLemma

variable {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n)
variable {M : Type} [AddCommGroup M] [Module B M]

theorem e_smul_of_mem_corner (j k : Fin S.n) {v : M} (hv : v ∈ cornerSubmodule (M := M) (S.e k)) :
    S.e j • v = if j = k then v else 0 := by
  have hv' : S.e k • v = v := S.e_smul_coe k ⟨v, hv⟩
  calc S.e j • v = S.e j • (S.e k • v) := by rw [hv']
    _ = (S.e j * S.e k) • v := smul_smul _ _ _
    _ = if j = k then v else 0 := by
        rw [S.coi.mul_eq]
        split_ifs with h
        · subst h; exact hv'
        · exact zero_smul _ _

noncomputable def cornerRestrict (f : M →ₗ[B] M) :
    ↥(cornerSubmodule (M := M) (S.e i)) →ₗ[S.CornerRing i] ↥(cornerSubmodule (M := M) (S.e i)) where
  toFun x := ⟨f (x : M), by
    refine ⟨f (x : M), ?_⟩
    show S.e i • f (x : M) = f (x : M)
    rw [← map_smul, S.e_smul_coe]⟩
  map_add' x y := Subtype.ext (by
    show f ((x : M) + (y : M)) = f (x : M) + f (y : M)
    exact map_add f _ _)
  map_smul' z x := Subtype.ext (by
    show f ((z : B) • (x : M)) = (z : B) • f (x : M)
    exact map_smul f _ _)

theorem coe_cornerRestrict (f : M →ₗ[B] M) (x : cornerSubmodule (M := M) (S.e i)) :
    ((cornerRestrict S i f x : cornerSubmodule (M := M) (S.e i)) : M) = f x := rfl

theorem exists_smul_add_smul_of_corner (v0 v1 : cornerSubmodule (M := M) (S.e i))
    (hsp : ∀ x : cornerSubmodule (M := M) (S.e i), ∃ z0 z1 : S.CornerRing i, x = z0 • v0 + z1 • v1)
    (m : M) (hm : m ∈ cornerSubmodule (M := M) (S.e i)) :
    ∃ r s : B, m = r • (v0 : M) + s • (v1 : M) := by
  obtain ⟨z0, z1, hx⟩ := hsp ⟨m, hm⟩
  refine ⟨z0, z1, ?_⟩
  have := congrArg Subtype.val hx
  simpa only [Submodule.coe_add, IdempotentSplitting.coe_cornerSmul] using this

theorem mul_e_eq_zero_of_corner (v0 v1 : cornerSubmodule (M := M) (S.e i))
    (hind : ∀ z0 z1 : S.CornerRing i, z0 • v0 + z1 • v1 = 0 → z0 = 0 ∧ z1 = 0)
    (r s : B) (h : r • (v0 : M) + s • (v1 : M) = 0) : r * S.e i = 0 ∧ s * S.e i = 0 := by
  have hz : S.toCornerRing i r • v0 + S.toCornerRing i s • v1 = 0 := by
    apply Subtype.ext
    have h' := congrArg (S.e i • ·) h
    simp only [smul_add, smul_zero, smul_smul] at h'
    rw [Submodule.coe_add, IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_cornerSmul,
      IdempotentSplitting.coe_toCornerRing, IdempotentSplitting.coe_toCornerRing, Submodule.coe_zero,
      mul_smul (S.e i * r) (S.e i), S.e_smul_coe, mul_smul (S.e i * s) (S.e i), S.e_smul_coe]
    exact h'
  obtain ⟨h0, h1⟩ := hind _ _ hz
  have e0 : S.e i * r * S.e i = 0 := congrArg Subtype.val h0
  have e1 : S.e i * s * S.e i = 0 := congrArg Subtype.val h1
  refine ⟨?_, ?_⟩
  · calc r * S.e i = S.e i * r * S.e i := by rw [mul_comm (S.e i) r, mul_assoc, (S.idem i).eq]
      _ = 0 := e0
  · calc s * S.e i = S.e i * s * S.e i := by rw [mul_comm (S.e i) s, mul_assoc, (S.idem i).eq]
      _ = 0 := e1

theorem glue (J : Finset (Fin S.n)) (v0 v1 : Fin S.n → M)
    (hv0 : ∀ j, v0 j ∈ cornerSubmodule (M := M) (S.e j)) (hv1 : ∀ j, v1 j ∈ cornerSubmodule (M := M) (S.e j))
    (hspan : ∀ j ∈ J, ∀ m ∈ cornerSubmodule (M := M) (S.e j), ∃ r s : B, m = r • v0 j + s • v1 j)
    (hind : ∀ j ∈ J, ∀ r s : B, r • v0 j + s • v1 j = 0 → r * S.e j = 0 ∧ s * S.e j = 0) :
    (∀ m : M, (∀ j, j ∉ J → S.e j • m = 0) →
        ∃ r s : B, m = r • (∑ j ∈ J, v0 j) + s • (∑ j ∈ J, v1 j)) ∧
    (∀ r s : B, r • (∑ j ∈ J, v0 j) + s • (∑ j ∈ J, v1 j) = 0 → ∀ j ∈ J, r * S.e j = 0 ∧ s * S.e j = 0) ∧
    (∀ j ∈ J, S.e j • (∑ k ∈ J, v0 k) = v0 j) ∧ (∀ j ∈ J, S.e j • (∑ k ∈ J, v1 k) = v1 j) ∧
    (∀ j, j ∉ J → S.e j • (∑ k ∈ J, v0 k) = 0) ∧ (∀ j, j ∉ J → S.e j • (∑ k ∈ J, v1 k) = 0) := by
  classical
  have hin : ∀ (v : Fin S.n → M), (∀ j, v j ∈ cornerSubmodule (M := M) (S.e j)) →
      ∀ j ∈ J, S.e j • (∑ k ∈ J, v k) = v j := by
    intro v hv j hj
    rw [Finset.smul_sum, Finset.sum_eq_single_of_mem j hj]
    · rw [e_smul_of_mem_corner S j j (hv j), if_pos rfl]
    · intro k _ hkj
      rw [e_smul_of_mem_corner S j k (hv k), if_neg (Ne.symm hkj)]
  have hout : ∀ (v : Fin S.n → M), (∀ j, v j ∈ cornerSubmodule (M := M) (S.e j)) →
      ∀ j, j ∉ J → S.e j • (∑ k ∈ J, v k) = 0 := by
    intro v hv j hj
    rw [Finset.smul_sum]
    exact Finset.sum_eq_zero fun k hk => by
      rw [e_smul_of_mem_corner S j k (hv k), if_neg (fun h : j = k => hj (h ▸ hk))]
  refine ⟨?_, ?_, hin v0 hv0, hin v1 hv1, hout v0 hv0, hout v1 hv1⟩
  · intro m hm
    have hex : ∀ j, ∃ r s : B, j ∈ J → S.e j • m = r • v0 j + s • v1 j := by
      intro j
      by_cases hj : j ∈ J
      · obtain ⟨r, s, h⟩ := hspan j hj (S.e j • m) ⟨m, rfl⟩
        exact ⟨r, s, fun _ => h⟩
      · exact ⟨0, 0, fun h => absurd h hj⟩
    choose r s hrs using hex
    refine ⟨∑ j ∈ J, r j * S.e j, ∑ j ∈ J, s j * S.e j, ?_⟩
    symm
    calc (∑ j ∈ J, r j * S.e j) • (∑ k ∈ J, v0 k) + (∑ j ∈ J, s j * S.e j) • (∑ k ∈ J, v1 k)
        = ∑ j ∈ J, (r j * S.e j) • (∑ k ∈ J, v0 k) + ∑ j ∈ J, (s j * S.e j) • (∑ k ∈ J, v1 k) := by
          rw [Finset.sum_smul, Finset.sum_smul]
      _ = ∑ j ∈ J, r j • v0 j + ∑ j ∈ J, s j • v1 j := by
          congr 1
          · exact Finset.sum_congr rfl fun j hj => by rw [mul_smul, hin v0 hv0 j hj]
          · exact Finset.sum_congr rfl fun j hj => by rw [mul_smul, hin v1 hv1 j hj]
      _ = ∑ j ∈ J, S.e j • m := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j hj => (hrs j hj).symm
      _ = ∑ j, S.e j • m := Finset.sum_subset (Finset.subset_univ J) fun j _ hj => hm j hj
      _ = m := by rw [← Finset.sum_smul, S.coi.complete, one_smul]
  · intro r s h j hj
    apply hind j hj
    have h' := congrArg (S.e j • ·) h
    simp only [smul_add, smul_zero, smul_smul] at h'
    rwa [mul_comm (S.e j) r, mul_comm (S.e j) s, mul_smul, mul_smul, hin v0 hv0 j hj,
      hin v1 hv1 j hj] at h'

end OrdLat.Corner
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"

namespace OrdLat
namespace FreeLocal

theorem exists_generator_of_finrank_eq_one {C : Type} [CommRing C] [Nontrivial C] {L : Type} [AddCommGroup L]
    [Module C L] [Module.Free C L] [Module.Finite C L] (h : Module.finrank C L = 1) :
    ∃ v : L, (∀ x : L, ∃ c : C, x = c • v) ∧ (∀ c : C, c • v = 0 → c = 0) := by
  let b := Module.Free.chooseBasis C L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex C L) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, h]
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.mp hcard
  refine ⟨b i0, fun x => ⟨b.repr x i0, ?_⟩, fun c hc => ?_⟩
  · conv_lhs => rw [← b.sum_repr x]
    rw [Fintype.sum_eq_single i0 (fun j hj => absurd (hi0 j) hj)]
  · have := congrArg (fun y => b.repr y i0) hc
    simpa using this

theorem basis_pair_of_isCompl {C : Type} [CommRing C] {N : Type} [AddCommGroup N] [Module C N]
    (N0 N1 : Submodule C N) (h : IsCompl N0 N1) (v0 v1 : N) (hv0 : v0 ∈ N0) (hv1 : v1 ∈ N1)
    (hg0 : ∀ x ∈ N0, ∃ c : C, x = c • v0) (ha0 : ∀ c : C, c • v0 = 0 → c = 0)
    (hg1 : ∀ x ∈ N1, ∃ c : C, x = c • v1) (ha1 : ∀ c : C, c • v1 = 0 → c = 0) :
    (∀ x : N, ∃ c d : C, x = c • v0 + d • v1) ∧ (∀ c d : C, c • v0 + d • v1 = 0 → c = 0 ∧ d = 0) := by
  refine ⟨fun x => ?_, fun c d hcd => ?_⟩
  · have hx : x ∈ N0 ⊔ N1 := by rw [h.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := hg0 y hy
    obtain ⟨d, rfl⟩ := hg1 z hz
    exact ⟨c, d, rfl⟩
  · have h0 : c • v0 ∈ N0 := N0.smul_mem c hv0
    have h1 : d • v1 ∈ N1 := N1.smul_mem d hv1
    have hc0 : c • v0 = -(d • v1) := eq_neg_of_add_eq_zero_left hcd
    have hmem : c • v0 ∈ N1 := by rw [hc0]; exact N1.neg_mem h1
    have hz0 : c • v0 = 0 := Submodule.disjoint_def.mp h.disjoint _ h0 hmem
    have hz1 : d • v1 = 0 := by rwa [hz0, zero_add] at hcd
    exact ⟨ha0 c hz0, ha1 d hz1⟩

end OrdLat.FreeLocal
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"

namespace OrdLat

section RankParity2

theorem finrank_eigenspaces_of_similitude {K : Type} [Field K] {N : Type} [AddCommGroup N] [Module K N]
    [FiniteDimensional K N] (h2 : (2 : K) ≠ 0) (s g : N →ₗ[K] N) (hs : ∀ x, s (s x) = x)
    (B : N →ₗ[K] N →ₗ[K] K) (hB : ∀ x, (∀ y, B x y = 0) → x = 0)
    (u : K) (hu : u * (u - 1) ≠ 0)
    (hg0 : ∀ x, s x = -x → g x = u • x) (hg1 : ∀ x, s (g x - x) = -(g x - x))
    (hsim : ∀ x y, B (g x) (g y) = u * B x y) :
    Module.finrank K (LinearMap.ker (s + LinearMap.id)) =
      Module.finrank K (LinearMap.ker (s - LinearMap.id)) := by
  have hc := isCompl_eigenspaces_of_involution s hs (isUnit_iff_ne_zero.mpr h2)
  refine finrank_eq_of_similitude _ _ hc B hB g u hu ?_ ?_ hsim
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at hx
    exact hg0 x (eq_neg_of_add_eq_zero_left hx)
  · intro x
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, hg1, neg_add_cancel]

theorem generators_of_involution {K : Type} [Field K] {C : Type} [CommRing C] [IsLocalRing C] [Algebra K C]
    [Module.Finite K C] {N : Type} [AddCommGroup N] [Module C N] [Module K N] [IsScalarTower K C N]
    (bN : Module.Basis (Fin 2) C N) (s : N →ₗ[C] N) (hs : ∀ x, s (s x) = x) (h2 : IsUnit (2 : C))
    (hdim : Module.finrank K (LinearMap.ker (s.restrictScalars K + LinearMap.id)) =
      Module.finrank K (LinearMap.ker (s.restrictScalars K - LinearMap.id))) :
    ∃ v0 v1 : N, s v0 = -v0 ∧ s v1 = v1 ∧ (∀ x : N, ∃ c d : C, x = c • v0 + d • v1) ∧
      (∀ c d : C, c • v0 + d • v1 = 0 → c = 0 ∧ d = 0) := by
  set N0 : Submodule C N := LinearMap.ker (s + (LinearMap.id : N →ₗ[C] N)) with hN0
  set N1 : Submodule C N := LinearMap.ker (s - (LinearMap.id : N →ₗ[C] N)) with hN1
  have hc : IsCompl N0 N1 := isCompl_eigenspaces_of_involution s hs h2
  haveI : Module.Free C N := Module.Free.of_basis bN
  haveI : Module.Finite C N := Module.Finite.of_basis bN
  have hrk : Module.finrank C N = 2 := by rw [Module.finrank_eq_card_basis bN, Fintype.card_fin]
  have hH2b := IsLocalRing.free_and_finrank_add_eq_of_isCompl N0 N1 hc
  obtain ⟨hfree0, hfin0, hfree1, hfin1, hsum⟩ := hH2b
  rw [hrk] at hsum

  have e0 : LinearMap.ker (s.restrictScalars K + LinearMap.id) ≃ₗ[K] N0 :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e1 : LinearMap.ker (s.restrictScalars K - LinearMap.id) ≃ₗ[K] N1 :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e0.finrank_eq, e1.finrank_eq] at hdim
  haveI := hfree0; haveI := hfin0; haveI := hfree1; haveI := hfin1
  have ht0 : Module.finrank K N0 = Module.finrank K C * Module.finrank C N0 :=
    (Module.finrank_mul_finrank K C N0).symm
  have ht1 : Module.finrank K N1 = Module.finrank K C * Module.finrank C N1 :=
    (Module.finrank_mul_finrank K C N1).symm
  have hdpos : 0 < Module.finrank K C := Module.finrank_pos
  have heq : Module.finrank C N0 = Module.finrank C N1 := by
    apply Nat.eq_of_mul_eq_mul_left hdpos
    rw [← ht0, ← ht1, hdim]
  have hr0 : Module.finrank C N0 = 1 := by omega
  have hr1 : Module.finrank C N1 = 1 := by omega
  obtain ⟨g0, hg0gen, hg0ann⟩ := OrdLat.FreeLocal.exists_generator_of_finrank_eq_one hr0
  obtain ⟨g1, hg1gen, hg1ann⟩ := OrdLat.FreeLocal.exists_generator_of_finrank_eq_one hr1
  obtain ⟨hspan, hind⟩ := OrdLat.FreeLocal.basis_pair_of_isCompl N0 N1 hc (g0 : N) (g1 : N) g0.2 g1.2
    (fun x hx => by obtain ⟨c, hc⟩ := hg0gen ⟨x, hx⟩; exact ⟨c, congrArg Subtype.val hc⟩)
    (fun c hc => hg0ann c (Subtype.ext hc))
    (fun x hx => by obtain ⟨c, hc⟩ := hg1gen ⟨x, hx⟩; exact ⟨c, congrArg Subtype.val hc⟩)
    (fun c hc => hg1ann c (Subtype.ext hc))
  refine ⟨g0, g1, ?_, ?_, hspan, hind⟩
  · have h : s (g0 : N) + (g0 : N) = 0 := g0.2
    exact eq_neg_of_add_eq_zero_left h
  · have h : s (g1 : N) - (g1 : N) = 0 := g1.2
    exact sub_eq_zero.mp h

end RankParity2
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"

end OrdLat
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"

namespace OrdLat

section Factors

open IharaLemma

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
variable {ι₀ : Type} {A : ι₀ → Module.End ℤ_[p] T}
variable [IsMulCommutative (R p T A)]

theorem idem_eq_zero_or_one {C : Type} [CommRing C] [IsLocalRing C] {z : C} (hz : IsIdempotentElem z) :
    z = 0 ∨ z = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self z with h | h
  · right
    obtain ⟨w, hw⟩ := h
    have : (w : C) * w = w := by rw [hw]; exact hz.eq
    have h1 : (w : C) = 1 := by
      have := congrArg (fun t => ((w⁻¹ : Cˣ) : C) * t) this
      simpa [← mul_assoc] using this
    rw [← hw, h1]
  · left
    obtain ⟨w, hw⟩ := h
    have hz' : IsIdempotentElem (1 - z) := hz.one_sub
    have : (w : C) * w = w := by rw [hw]; exact hz'.eq
    have h1 : (w : C) = 1 := by
      have := congrArg (fun t => ((w⁻¹ : Cˣ) : C) * t) this
      simpa [← mul_assoc] using this
    have : (1 : C) - z = 1 := by rw [← hw, h1]
    simpa using this

variable (SR : IdempotentSplitting (R p T A))

theorem mul_e_eq_or (er : R p T A) (her : IsIdempotentElem er) (j : Fin SR.n) :
    er * SR.e j = SR.e j ∨ er * SR.e j = 0 := by
  have hz : IsIdempotentElem (SR.toCornerRing j er) := her.map _
  rcases idem_eq_zero_or_one (C := SR.CornerRing j) hz with h | h
  · right
    have h' : SR.e j * er * SR.e j = 0 := congrArg Subtype.val h
    rw [mul_comm (SR.e j) er, mul_assoc, (SR.idem j).eq] at h'
    exact h'
  · left
    have h' : SR.e j * er * SR.e j = SR.e j := congrArg Subtype.val h
    rw [mul_comm (SR.e j) er, mul_assoc, (SR.idem j).eq] at h'
    exact h'

open Classical in

theorem eq_sum_e (er : R p T A) (her : IsIdempotentElem er) :
    er = ∑ j ∈ Finset.univ.filter (fun j => er * SR.e j = SR.e j), SR.e j := by
  rw [Finset.sum_filter]
  calc er = er * ∑ j, SR.e j := by rw [SR.coi.complete, mul_one]
    _ = ∑ j, er * SR.e j := Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun j _ => by
      rcases mul_e_eq_or SR er her j with h | h
      · rw [if_pos h, h]
      · rw [if_neg ?_, h]
        intro h'
        rw [h] at h'
        exact SR.notMem j (h' ▸ Submodule.zero_mem _)

theorem coe_e_apply_of_mem (j : Fin SR.n) {v : V p T} (hv : v ∈ cornerSubmodule (M := V p T) (SR.e j)) :
    (SR.e j : Module.End ℚ_[p] (V p T)) v = v := by
  obtain ⟨z, rfl⟩ := hv
  show ((SR.e j * SR.e j : R p T A) : Module.End ℚ_[p] (V p T)) z = (SR.e j : Module.End ℚ_[p] (V p T)) z
  rw [(SR.idem j).eq]

theorem er_apply_of_mem (er : R p T A) (j : Fin SR.n) (hj : er * SR.e j = SR.e j) {v : V p T}
    (hv : v ∈ cornerSubmodule (M := V p T) (SR.e j)) : (er : Module.End ℚ_[p] (V p T)) v = v := by
  have h := coe_e_apply_of_mem SR j hv
  conv_lhs => rw [← h]
  rw [← Module.End.mul_apply]
  show ((er * SR.e j : R p T A) : Module.End ℚ_[p] (V p T)) v = v
  rw [hj]
  exact h

theorem factor_generators
    (er : R p T A) (her : IsIdempotentElem er) (j : Fin SR.n) (hj : er * SR.e j = SR.e j)
    (s0 t1 : Module.End ℤ_[p] T)
    (hs0A : ∀ (g : ι₀) (x : T), s0 (A g x) = A g (s0 x)) (ht1A : ∀ (g : ι₀) (x : T), t1 (A g x) = A g (t1 x))
    (u : ℚ_[p]) (hu : u * (u - 1) ≠ 0)
    (hsW : ∀ v : V p T, (er : Module.End ℚ_[p] (V p T)) v = v → bc p T s0 (bc p T s0 v) = v)
    (ht0W : ∀ v : V p T, (er : Module.End ℚ_[p] (V p T)) v = v → bc p T s0 v = -v → bc p T t1 v = u • v)
    (ht1W : ∀ v : V p T, (er : Module.End ℚ_[p] (V p T)) v = v →
      bc p T s0 (bc p T t1 v - v) = -(bc p T t1 v - v))
    (b : Module.Basis (Fin 2) (R p T A) (V p T))
    (Bf : V p T →ₗ[ℚ_[p]] V p T →ₗ[ℚ_[p]] ℚ_[p]) (hBnd : ∀ x, (∀ y, Bf x y = 0) → x = 0)
    (hBselfR : ∀ r : R p T A, ∀ x y : V p T, Bf ((r : Module.End ℚ_[p] (V p T)) x) y =
      Bf x ((r : Module.End ℚ_[p] (V p T)) y))
    (hBsim : ∀ x y, Bf (bc p T t1 x) (bc p T t1 y) = u * Bf x y)
    [Module.Finite ℚ_[p] (SR.CornerRing j)] :
    ∃ v0 v1 : V p T, v0 ∈ cornerSubmodule (M := V p T) (SR.e j) ∧ v1 ∈ cornerSubmodule (M := V p T) (SR.e j) ∧
      bc p T s0 v0 = -v0 ∧ bc p T s0 v1 = v1 ∧
      (∀ m ∈ cornerSubmodule (M := V p T) (SR.e j), ∃ r s : R p T A, m = r • v0 + s • v1) ∧
      (∀ r s : R p T A, r • v0 + s • v1 = 0 → r * SR.e j = 0 ∧ s * SR.e j = 0) := by
  classical
  set Vj := cornerSubmodule (M := V p T) (SR.e j) with hVj
  have hW : ∀ v ∈ Vj, (er : Module.End ℚ_[p] (V p T)) v = v := fun v hv => er_apply_of_mem SR er j hj hv

  let sj : Vj →ₗ[SR.CornerRing j] Vj := OrdLat.Corner.cornerRestrict SR j (toRLin A s0 hs0A)
  let tj : Vj →ₗ[SR.CornerRing j] Vj := OrdLat.Corner.cornerRestrict SR j (toRLin A t1 ht1A)
  have hsj_coe : ∀ x : Vj, ((sj x : Vj) : V p T) = bc p T s0 x := fun x => rfl
  have htj_coe : ∀ x : Vj, ((tj x : Vj) : V p T) = bc p T t1 x := fun x => rfl
  have hsj : ∀ x : Vj, sj (sj x) = x := fun x => Subtype.ext (by rw [hsj_coe, hsj_coe]; exact hsW _ (hW _ x.2))
  have h2 : IsUnit (2 : SR.CornerRing j) := by
    have : (2 : SR.CornerRing j) = algebraMap ℚ_[p] (SR.CornerRing j) 2 := by rw [map_ofNat]
    rw [this]
    exact (isUnit_iff_ne_zero.mpr two_ne_zero).map _

  let sjK : Vj →ₗ[ℚ_[p]] Vj := sj.restrictScalars ℚ_[p]
  let tjK : Vj →ₗ[ℚ_[p]] Vj := tj.restrictScalars ℚ_[p]
  have hsjK_coe : ∀ x : Vj, ((sjK x : Vj) : V p T) = bc p T s0 x := fun x => rfl
  have htjK_coe : ∀ x : Vj, ((tjK x : Vj) : V p T) = bc p T t1 x := fun x => rfl
  let ι : Vj →ₗ[ℚ_[p]] V p T := Vj.subtype.restrictScalars ℚ_[p]
  let BN : Vj →ₗ[ℚ_[p]] Vj →ₗ[ℚ_[p]] ℚ_[p] := Bf.compl₁₂ ι ι
  have hBN_apply : ∀ x y : Vj, BN x y = Bf (x : V p T) (y : V p T) := fun x y => rfl
  have hBN : ∀ x : Vj, (∀ y : Vj, BN x y = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    apply hBnd
    intro y'
    have hy' : (SR.e j : Module.End ℚ_[p] (V p T)) y' ∈ Vj := ⟨y', rfl⟩
    have := hx ⟨_, hy'⟩
    rw [hBN_apply] at this
    rw [← coe_e_apply_of_mem SR j x.2, hBselfR]
    exact this
  have hg0 : ∀ x : Vj, sjK x = -x → tjK x = u • x := by
    intro x hx
    apply Subtype.ext
    have hx' : bc p T s0 (x : V p T) = -(x : V p T) := by
      have := congrArg Subtype.val hx
      rw [hsjK_coe, Submodule.coe_neg] at this
      exact this
    rw [htjK_coe, Submodule.coe_smul_of_tower]
    exact ht0W _ (hW _ x.2) hx'
  have hg1 : ∀ x : Vj, sjK (tjK x - x) = -(tjK x - x) := by
    intro x
    apply Subtype.ext
    rw [hsjK_coe, Submodule.coe_sub, htjK_coe, Submodule.coe_neg, Submodule.coe_sub, htjK_coe]
    exact ht1W _ (hW _ x.2)
  have hsimN : ∀ x y : Vj, BN (tjK x) (tjK y) = u * BN x y := by
    intro x y
    rw [hBN_apply, hBN_apply, htjK_coe, htjK_coe]
    exact hBsim _ _

  have hH2a := IharaLemma.IdempotentSplitting.exists_basis_cornerSubmodule_coe_eq_smul SR j b
  obtain ⟨bj, -⟩ := hH2a
  haveI : Module.Free (SR.CornerRing j) Vj := Module.Free.of_basis bj
  haveI : Module.Finite (SR.CornerRing j) Vj := Module.Finite.of_basis bj
  haveI : Module.Finite ℚ_[p] Vj := Module.Finite.trans (SR.CornerRing j) Vj
  have hdim := finrank_eigenspaces_of_similitude (two_ne_zero) sjK tjK hsj BN hBN u hu hg0 hg1 hsimN
  obtain ⟨g0, g1, hs0, hs1, hspanj, hindj⟩ := generators_of_involution (K := ℚ_[p]) bj sj hsj h2 hdim
  refine ⟨(g0 : V p T), (g1 : V p T), g0.2, g1.2, ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val hs0
    rw [hsj_coe, Submodule.coe_neg] at this
    exact this
  · have := congrArg Subtype.val hs1
    rw [hsj_coe] at this
    exact this
  · intro m hm
    exact OrdLat.Corner.exists_smul_add_smul_of_corner SR j g0 g1
      (fun x => by obtain ⟨c, d, h⟩ := hspanj x; exact ⟨c, d, h⟩) m hm
  · intro r s h
    exact OrdLat.Corner.mul_e_eq_zero_of_corner SR j g0 g1 hindj r s h

end Factors
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"

end OrdLat
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"

namespace OrdLat

section Uniform

theorem exists_uniform_pow {Rg : Type} [CommRing Rg] {Mg : Type} [AddCommGroup Mg] [Module Rg Mg]
    (q : Rg) (P Q : Submodule Rg Mg) (hP : P.FG) (h : ∀ z ∈ P, ∃ n : ℕ, q ^ n • z ∈ Q) :
    ∃ N : ℕ, ∀ z ∈ P, q ^ N • z ∈ Q := by
  classical
  obtain ⟨s, hs⟩ := hP
  choose! n hn using h
  refine ⟨∑ z ∈ s, n z, ?_⟩
  intro z hz
  rw [← hs] at hz
  induction hz using Submodule.span_induction with
  | mem z hzs =>
    have hzP : z ∈ P := hs ▸ Submodule.subset_span hzs
    have hle : n z ≤ ∑ w ∈ s, n w := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hzs
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
    rw [hm, add_comm, pow_add, mul_smul]
    exact Q.smul_mem _ (hn z hzP)
  | zero => rw [smul_zero]; exact Q.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Q.add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Q.smul_mem c hx

end Uniform
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"

section CoreThm

open IharaLemma

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
variable {ι₀ : Type} {A : ι₀ → Module.End ℤ_[p] T}
variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]

theorem p_ne_zero_Q : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem castpow (n : ℕ) : (((p : ℤ_[p]) ^ n : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ n := by
  push_cast
  rfl

theorem core
    (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0)
    (op : ι₀ → 𝕋) (hop : ∀ (g : ι₀) (x : T), op g • x = A g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (P0 : Submodule 𝕋 T) (s0 t1 : Module.End ℤ_[p] T) (u : ℤ_[p]) (h2 : IsUnit (2 : ℤ_[p]))
    (hs0 : ∀ (t : 𝕋) (x : T), s0 (t • x) = t • s0 x) (ht1 : ∀ (t : 𝕋) (x : T), t1 (t • x) = t • t1 x)
    (hP0 : ∀ x, x ∈ P0 ↔ x ∈ cornerSubmodule (M := T) (S'.e i₀) ∧ s0 x = -x)
    (hsq : ∀ x ∈ cornerSubmodule (M := T) (S'.e i₀), s0 (s0 x) = x)
    (ht1P0 : ∀ x ∈ P0, t1 x = u • x)
    (ht1unr : ∀ x ∈ cornerSubmodule (M := T) (S'.e i₀), t1 x - x ∈ P0)
    (b : Module.Basis (Fin 2) (R p T A) (V p T))
    (Bf : V p T →ₗ[ℚ_[p]] V p T →ₗ[ℚ_[p]] ℚ_[p]) (hBnd : ∀ x, (∀ y, Bf x y = 0) → x = 0)
    (hBself : ∀ (g : ι₀) (x y : V p T), Bf (bc p T (A g) x) y = Bf x (bc p T (A g) y))
    (hBsim : ∀ x y, Bf (bc p T t1 x) (bc p T t1 y) = (u : ℚ_[p]) * Bf x y)
    (hu : (u : ℚ_[p]) * ((u : ℚ_[p]) - 1) ≠ 0) :
    ∃ (x₀ y : T) (N : ℕ), x₀ ∈ P0 ∧ y ∈ cornerSubmodule (M := T) (S'.e i₀) ∧ s0 y = y ∧
      (∀ a b : S'.CornerRing i₀, ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y = 0 →
        a = 0 ∧ b = 0) ∧
      (∀ z ∈ cornerSubmodule (M := T) (S'.e i₀), ∃ a b : S'.CornerRing i₀,
        ((p : ℤ_[p]) ^ N) • z = ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y) ∧
      (∀ z ∈ P0, ∃ a : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z = ((a : S'.CornerRing i₀) : 𝕋) • x₀) ∧
      (∀ z ∈ cornerSubmodule (M := T) (S'.e i₀), s0 z = z →
        ∃ b : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z = ((b : S'.CornerRing i₀) : 𝕋) • y) := by
  classical
  haveI : IsMulCommutative (R p T A) := isMulCommutative_R A op hop

  haveI : Module.Finite ℚ_[p] (V p T) := inferInstance
  haveI : IsNoetherian ℚ_[p] (Module.End ℚ_[p] (V p T)) := isNoetherian_of_isNoetherianRing_of_finite ℚ_[p] _
  haveI : Module.Finite ℚ_[p] (R p T A) :=
    Module.Finite.of_injective (R p T A).val.toLinearMap Subtype.val_injective
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ℚ_[p]) ℚ_[p] := by
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp (Field.toIsField ℚ_[p])]
    infer_instance
  obtain ⟨SR⟩ := IharaLemma.nonempty_idempotentSplitting_of_finite ℚ_[p] (R p T A)
  haveI : ∀ j, Module.Finite ℚ_[p] (SR.CornerRing j) := fun j =>
    IharaLemma.IdempotentSplitting.finite_cornerRing (𝒪 := ℚ_[p]) SR j
  haveI : IsNoetherian ℤ_[p] T := isNoetherian_of_isNoetherianRing_of_finite ℤ_[p] T

  set er : R p T A := ⟨ψ p T 𝕋 (S'.e i₀), ψ_mem_R A op hop hgen _⟩ with her_def
  have her_coe : (er : Module.End ℚ_[p] (V p T)) = ψ p T 𝕋 (S'.e i₀) := rfl
  have her : IsIdempotentElem er := by
    apply Subtype.ext
    show ψ p T 𝕋 (S'.e i₀) * ψ p T 𝕋 (S'.e i₀) = ψ p T 𝕋 (S'.e i₀)
    rw [← map_mul, (S'.idem i₀).eq]
  set J : Finset (Fin SR.n) := Finset.univ.filter (fun j => er * SR.e j = SR.e j) with hJ
  have hsumJ : er = ∑ j ∈ J, SR.e j := eq_sum_e SR er her
  have hp0 : (p : ℚ_[p]) ≠ 0 := p_ne_zero_Q
  have hs0A := comm_A_of_comm_𝕋 hop s0 hs0
  have ht1A := comm_A_of_comm_𝕋 hop t1 ht1

  have hsW : ∀ v : V p T, (er : Module.End ℚ_[p] (V p T)) v = v → bc p T s0 (bc p T s0 v) = v := by
    intro v hv
    obtain ⟨k, x, hx⟩ := exists_pow_smul_eq_toV (p := p) v
    have hxP := mem_corner_of_toV S' i₀ hv hx
    apply smul_right_injective (V p T) (pow_ne_zero k hp0)
    show ((p : ℚ_[p]) ^ k) • bc p T s0 (bc p T s0 v) = ((p : ℚ_[p]) ^ k) • v
    rw [← map_smul, ← map_smul, hx, bc_toV, bc_toV, hsq x hxP]
  have ht0W : ∀ v : V p T, (er : Module.End ℚ_[p] (V p T)) v = v → bc p T s0 v = -v →
      bc p T t1 v = (u : ℚ_[p]) • v := by
    intro v hv hsv
    obtain ⟨k, x, hx⟩ := exists_pow_smul_eq_toV (p := p) v
    have hxP := mem_corner_of_toV S' i₀ hv hx
    have hsx : s0 x = -x := by
      have h := apply_eq_smul_of_toV (p := p) s0 (-1) (by rw [hsv]; simp) hx
      simpa using h
    have hx0 : x ∈ P0 := (hP0 x).mpr ⟨hxP, hsx⟩
    apply smul_right_injective (V p T) (pow_ne_zero k hp0)
    show ((p : ℚ_[p]) ^ k) • bc p T t1 v = ((p : ℚ_[p]) ^ k) • ((u : ℚ_[p]) • v)
    rw [← map_smul, hx, bc_toV, ht1P0 x hx0, toV_smul, smul_comm, hx]
  have ht1W : ∀ v : V p T, (er : Module.End ℚ_[p] (V p T)) v = v →
      bc p T s0 (bc p T t1 v - v) = -(bc p T t1 v - v) := by
    intro v hv
    obtain ⟨k, x, hx⟩ := exists_pow_smul_eq_toV (p := p) v
    have hxP := mem_corner_of_toV S' i₀ hv hx
    have hs : s0 (t1 x - x) = -(t1 x - x) := ((hP0 _).mp (ht1unr x hxP)).2
    have e1 : ((p : ℚ_[p]) ^ k) • (bc p T t1 v - v) = toV p T (t1 x - x) := by
      rw [smul_sub, ← map_smul, hx, bc_toV, map_sub]
    apply smul_right_injective (V p T) (pow_ne_zero k hp0)
    show ((p : ℚ_[p]) ^ k) • bc p T s0 (bc p T t1 v - v) = ((p : ℚ_[p]) ^ k) • -(bc p T t1 v - v)
    rw [← map_smul, e1, bc_toV, hs, map_neg, ← e1, smul_neg]
  have hBselfR : ∀ r : R p T A, ∀ x y : V p T, Bf ((r : Module.End ℚ_[p] (V p T)) x) y =
      Bf x ((r : Module.End ℚ_[p] (V p T)) y) := fun r => selfAdjoint_of_mem_R Bf hBself r.2

  have hfac : ∀ j, j ∈ J → ∃ v0 v1 : V p T, v0 ∈ cornerSubmodule (M := V p T) (SR.e j) ∧
      v1 ∈ cornerSubmodule (M := V p T) (SR.e j) ∧ bc p T s0 v0 = -v0 ∧ bc p T s0 v1 = v1 ∧
      (∀ m ∈ cornerSubmodule (M := V p T) (SR.e j), ∃ r s : R p T A, m = r • v0 + s • v1) ∧
      (∀ r s : R p T A, r • v0 + s • v1 = 0 → r * SR.e j = 0 ∧ s * SR.e j = 0) := by
    intro j hj
    exact factor_generators SR er her j (Finset.mem_filter.mp hj).2 s0 t1 hs0A ht1A (u : ℚ_[p]) hu
      hsW ht0W ht1W b Bf hBnd hBselfR hBsim
  choose! v0f v1f hv0f hv1f hs0v0 hs0v1 hspanf hindf using hfac

  set v0g : Fin SR.n → V p T := fun j => (SR.e j : Module.End ℚ_[p] (V p T)) (v0f j) with hv0g
  set v1g : Fin SR.n → V p T := fun j => (SR.e j : Module.End ℚ_[p] (V p T)) (v1f j) with hv1g
  have hv0g_mem : ∀ j, v0g j ∈ cornerSubmodule (M := V p T) (SR.e j) := fun j => ⟨v0f j, rfl⟩
  have hv1g_mem : ∀ j, v1g j ∈ cornerSubmodule (M := V p T) (SR.e j) := fun j => ⟨v1f j, rfl⟩
  have hv0g_eq : ∀ j ∈ J, v0g j = v0f j := fun j hj => coe_e_apply_of_mem SR j (hv0f j hj)
  have hv1g_eq : ∀ j ∈ J, v1g j = v1f j := fun j hj => coe_e_apply_of_mem SR j (hv1f j hj)
  obtain ⟨hglue_span, hglue_ind, hglue0, hglue1, hglue0', hglue1'⟩ :=
    OrdLat.Corner.glue SR J v0g v1g hv0g_mem hv1g_mem
      (fun j hj m hm => by rw [hv0g_eq j hj, hv1g_eq j hj]; exact hspanf j hj m hm)
      (fun j hj r s h => by rw [hv0g_eq j hj, hv1g_eq j hj] at h; exact hindf j hj r s h)
  set w0 := ∑ j ∈ J, v0g j with hw0
  set w1 := ∑ j ∈ J, v1g j with hw1

  have herw0 : (er : Module.End ℚ_[p] (V p T)) w0 = w0 := by
    rw [hw0, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    exact er_apply_of_mem SR er j (Finset.mem_filter.mp hj).2 (hv0g_mem j)
  have herw1 : (er : Module.End ℚ_[p] (V p T)) w1 = w1 := by
    rw [hw1, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    exact er_apply_of_mem SR er j (Finset.mem_filter.mp hj).2 (hv1g_mem j)
  have hsw0 : bc p T s0 w0 = -w0 := by
    rw [hw0, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hv0g_eq j hj]; exact hs0v0 j hj
  have hsw1 : bc p T s0 w1 = w1 := by
    rw [hw1, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hv1g_eq j hj]; exact hs0v1 j hj

  have hoffJ : ∀ v : V p T, (er : Module.End ℚ_[p] (V p T)) v = v → ∀ j, j ∉ J →
      SR.e j • v = 0 := by
    intro v hv j hj
    have h0 : er * SR.e j = 0 := by
      rcases mul_e_eq_or SR er her j with h | h
      · have hjJ : j ∈ J := by rw [hJ]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
        exact absurd hjJ hj
      · exact h
    rw [R_smul_def, ← hv, ← Module.End.mul_apply]
    show ((SR.e j * er : R p T A) : Module.End ℚ_[p] (V p T)) v = 0
    rw [mul_comm, h0]
    rfl

  obtain ⟨k0, x₀, hx0⟩ := exists_pow_smul_eq_toV (p := p) w0
  obtain ⟨k1, y, hy⟩ := exists_pow_smul_eq_toV (p := p) w1
  have hx0P : x₀ ∈ cornerSubmodule (M := T) (S'.e i₀) := mem_corner_of_toV S' i₀ herw0 hx0
  have hyP : y ∈ cornerSubmodule (M := T) (S'.e i₀) := mem_corner_of_toV S' i₀ herw1 hy
  have hsx0 : s0 x₀ = -x₀ := by
    have h := apply_eq_smul_of_toV (p := p) s0 (-1) (by rw [hsw0]; simp) hx0
    simpa using h
  have hsy : s0 y = y := by
    have h := apply_eq_smul_of_toV (p := p) s0 1 (by rw [hsw1]; simp) hy
    simpa using h
  have hx0P0 : x₀ ∈ P0 := (hP0 _).mpr ⟨hx0P, hsx0⟩

  have hind : ∀ a b : S'.CornerRing i₀,
      ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have hV : ((p : ℚ_[p]) ^ k0 • (⟨ψ p T 𝕋 a, ψ_mem_R A op hop hgen _⟩ : R p T A)) • w0 +
        ((p : ℚ_[p]) ^ k1 • (⟨ψ p T 𝕋 b, ψ_mem_R A op hop hgen _⟩ : R p T A)) • w1 = 0 := by
      have := congrArg (toV p T) hab
      rw [map_add, map_zero, ← ψ_toV, ← ψ_toV, ← hx0, ← hy, map_smul, map_smul] at this
      rw [R_smul_def, R_smul_def]
      simpa using this
    have key : ∀ (c : S'.CornerRing i₀) (k : ℕ),
        (∀ j ∈ J, ((p : ℚ_[p]) ^ k • (⟨ψ p T 𝕋 c, ψ_mem_R A op hop hgen _⟩ : R p T A)) * SR.e j = 0) →
        c = 0 := by
      intro c k hc
      have h1 : ((p : ℚ_[p]) ^ k • (⟨ψ p T 𝕋 c, ψ_mem_R A op hop hgen _⟩ : R p T A)) * er = 0 := by
        rw [hsumJ, Finset.mul_sum]
        exact Finset.sum_eq_zero hc
      have h2 : ((p : ℚ_[p]) ^ k) • ψ p T 𝕋 ((c : 𝕋) * S'.e i₀) = 0 := by
        have := congrArg Subtype.val h1
        rw [map_mul]
        simpa [smul_mul_assoc] using this
      rw [IdempotentSplitting.coe_mul_e] at h2
      rcases smul_eq_zero.mp h2 with h | h
      · exact absurd h (pow_ne_zero k hp0)
      · have : (c : 𝕋) = 0 := ψ_injective (p := p) (T := T) hfaith (by rw [h, map_zero])
        exact Subtype.ext this
    obtain hj := hglue_ind _ _ hV
    exact ⟨key a k0 fun j hj' => (hj j hj').1, key b k1 fun j hj' => (hj j hj').2⟩

  set Qsub : Submodule ℤ_[p] T := (Submodule.span 𝕋 ({x₀, y} : Set T)).restrictScalars ℤ_[p] with hQ
  have hQmem : ∀ z : T, z ∈ Qsub ↔ ∃ t₁ t₂ : 𝕋, t₁ • x₀ + t₂ • y = z := fun z => by
    rw [hQ, Submodule.restrictScalars_mem, Submodule.mem_span_pair]
  have hspan_elem : ∀ z ∈ cornerSubmodule (M := T) (S'.e i₀), ∃ n : ℕ, ((p : ℤ_[p]) ^ n) • z ∈ Qsub := by
    intro z hz
    have hzW : (er : Module.End ℚ_[p] (V p T)) (toV p T z) = toV p T z := by
      rw [her_coe, ψ_toV, (mem_corner_iff S' i₀ z).mp hz]
    obtain ⟨r, s, hrs⟩ := hglue_span (toV p T z) (hoffJ _ hzW)
    obtain ⟨c, t, ht⟩ := exists_pow_smul_eq_ψ A op hop r.2
    obtain ⟨d, t', ht'⟩ := exists_pow_smul_eq_ψ A op hop s.2
    refine ⟨c + d + k0 + k1, (hQmem _).mpr ⟨((p : ℤ_[p]) ^ (d + k1)) • t, ((p : ℤ_[p]) ^ (c + k0)) • t', ?_⟩⟩
    apply toV_injective (p := p)
    rw [toV_smul, castpow, map_add, smul_assoc, smul_assoc, toV_smul, toV_smul, ← ψ_toV, ← ψ_toV,
      castpow, castpow, ← hx0, ← hy, hrs, R_smul_def, R_smul_def]
    rw [map_smul, map_smul, ← ht, ← ht', LinearMap.smul_apply, LinearMap.smul_apply, smul_add]
    simp only [smul_smul, ← pow_add]
    congr 2 <;> ring
  have hFG : ((cornerSubmodule (M := T) (S'.e i₀)).restrictScalars ℤ_[p]).FG := IsNoetherian.noetherian _
  obtain ⟨N, hN⟩ := exists_uniform_pow (p : ℤ_[p]) _ Qsub hFG
    (fun z hz => hspan_elem z ((Submodule.restrictScalars_mem _ _ _).mp hz))
  have hspan : ∀ z ∈ cornerSubmodule (M := T) (S'.e i₀), ∃ a b : S'.CornerRing i₀,
      ((p : ℤ_[p]) ^ N) • z = ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y := by
    intro z hz
    obtain ⟨t₁, t₂, ht⟩ := (hQmem _).mp (hN z ((Submodule.restrictScalars_mem _ _ _).mpr hz))
    refine ⟨S'.toCornerRing i₀ t₁, S'.toCornerRing i₀ t₂, ?_⟩
    rw [toCornerRing_smul_of_mem S' i₀ t₁ hx0P, toCornerRing_smul_of_mem S' i₀ t₂ hyP, ht]

  have h2A : IsUnit (2 : S'.CornerRing i₀) := by
    have : (2 : S'.CornerRing i₀) = algebraMap ℤ_[p] (S'.CornerRing i₀) 2 := by rw [map_ofNat]
    rw [this]; exact h2.map _
  have hs0lin : ∀ (n : ℕ) (z : T), s0 (((p : ℤ_[p]) ^ n) • z) = ((p : ℤ_[p]) ^ n) • s0 z := fun n z =>
    LinearMap.map_smul _ _ _
  refine ⟨x₀, y, N, hx0P0, hyP, hsy, hind, hspan, ?_, ?_⟩
  · intro z hz
    obtain ⟨hzP, hsz⟩ := (hP0 z).mp hz
    obtain ⟨a, b', hab⟩ := hspan z hzP
    refine ⟨a, ?_⟩
    have h0 : ((0 : S'.CornerRing i₀) : 𝕋) • x₀ + (((2 : S'.CornerRing i₀) * b' : S'.CornerRing i₀) : 𝕋) • y = 0 := by
      have e1 : ((p : ℤ_[p]) ^ N) • z + s0 (((p : ℤ_[p]) ^ N) • z) = 0 := by rw [hs0lin, hsz, smul_neg, add_neg_cancel]
      rw [hab, map_add, hs0, hs0, hsx0, hsy, smul_neg] at e1
      have e2 : (((2 : S'.CornerRing i₀) * b' : S'.CornerRing i₀) : 𝕋) • y =
          ((b' : S'.CornerRing i₀) : 𝕋) • y + ((b' : S'.CornerRing i₀) : 𝕋) • y := by
        rw [two_mul]
        show ((b' + b' : S'.CornerRing i₀) : 𝕋) • y = _
        rw [show ((b' + b' : S'.CornerRing i₀) : 𝕋) = (b' : 𝕋) + (b' : 𝕋) from rfl, add_smul]
      rw [e2, show ((0 : S'.CornerRing i₀) : 𝕋) = 0 from rfl, zero_smul, zero_add]
      have : ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b' : S'.CornerRing i₀) : 𝕋) • y +
          (-(((a : S'.CornerRing i₀) : 𝕋) • x₀) + ((b' : S'.CornerRing i₀) : 𝕋) • y) =
          ((b' : S'.CornerRing i₀) : 𝕋) • y + ((b' : S'.CornerRing i₀) : 𝕋) • y := by abel
      rw [← this]; exact e1
    have hb' : b' = 0 := by
      have := (hind 0 _ h0).2
      exact (h2A.mul_right_eq_zero).mp this
    rw [hab, hb', show ((0 : S'.CornerRing i₀) : 𝕋) = 0 from rfl, zero_smul, add_zero]
  · intro z hzP hsz
    obtain ⟨a', b, hab⟩ := hspan z hzP
    refine ⟨b, ?_⟩
    have h0 : (((2 : S'.CornerRing i₀) * a' : S'.CornerRing i₀) : 𝕋) • x₀ + ((0 : S'.CornerRing i₀) : 𝕋) • y = 0 := by
      have e1 : ((p : ℤ_[p]) ^ N) • z - s0 (((p : ℤ_[p]) ^ N) • z) = 0 := by rw [hs0lin, hsz, sub_self]
      rw [hab, map_add, hs0, hs0, hsx0, hsy, smul_neg] at e1
      have e2 : (((2 : S'.CornerRing i₀) * a' : S'.CornerRing i₀) : 𝕋) • x₀ =
          ((a' : S'.CornerRing i₀) : 𝕋) • x₀ + ((a' : S'.CornerRing i₀) : 𝕋) • x₀ := by
        rw [two_mul]
        show ((a' + a' : S'.CornerRing i₀) : 𝕋) • x₀ = _
        rw [show ((a' + a' : S'.CornerRing i₀) : 𝕋) = (a' : 𝕋) + (a' : 𝕋) from rfl, add_smul]
      rw [e2, show ((0 : S'.CornerRing i₀) : 𝕋) = 0 from rfl, zero_smul, add_zero]
      have : ((a' : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y -
          (-(((a' : S'.CornerRing i₀) : 𝕋) • x₀) + ((b : S'.CornerRing i₀) : 𝕋) • y) =
          ((a' : S'.CornerRing i₀) : 𝕋) • x₀ + ((a' : S'.CornerRing i₀) : 𝕋) • x₀ := by abel
      rw [← this]; exact e1
    have ha' : a' = 0 := by
      have := (hind _ 0 h0).1
      exact (h2A.mul_right_eq_zero).mp this
    rw [hab, ha', show ((0 : S'.CornerRing i₀) : 𝕋) = 0 from rfl, zero_smul, zero_add]

end CoreThm
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"

end OrdLat
p2m_reactivate "P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.OrdLat"

theorem solution
    (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] {ι₀ : Type} (A : ι₀ → Module.End ℤ_[p] T)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]
    (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0)
    (op : ι₀ → 𝕋) (hop : ∀ (g : ι₀) (x : T), op g • x = A g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (P0 : Submodule 𝕋 T) (s0 t1 : Module.End ℤ_[p] T) (u : ℤ_[p]) (h2 : IsUnit (2 : ℤ_[p]))
    (hs0 : ∀ (t : 𝕋) (x : T), s0 (t • x) = t • s0 x) (ht1 : ∀ (t : 𝕋) (x : T), t1 (t • x) = t • t1 x)
    (hP0 : ∀ x : T, x ∈ P0 ↔ x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀) ∧ s0 x = -x)
    (hsq : ∀ x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀), s0 (s0 x) = x)
    (ht1P0 : ∀ x ∈ P0, t1 x = u • x)
    (ht1unr : ∀ x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀), t1 x - x ∈ P0)
    (b : Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : ι₀ => (A g).baseChange ℚ_[p]))
      (TensorProduct ℤ_[p] ℚ_[p] T))
    (B : TensorProduct ℤ_[p] ℚ_[p] T →ₗ[ℚ_[p]] TensorProduct ℤ_[p] ℚ_[p] T →ₗ[ℚ_[p]] ℚ_[p])
    (hBnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hBself : ∀ (g : ι₀) (x y : TensorProduct ℤ_[p] ℚ_[p] T),
      B ((A g).baseChange ℚ_[p] x) y = B x ((A g).baseChange ℚ_[p] y))
    (hBsim : ∀ x y : TensorProduct ℤ_[p] ℚ_[p] T,
      B (t1.baseChange ℚ_[p] x) (t1.baseChange ℚ_[p] y) = ((u : ℤ_[p]) : ℚ_[p]) * B x y)
    (hu : ((u : ℤ_[p]) : ℚ_[p]) * (((u : ℤ_[p]) : ℚ_[p]) - 1) ≠ 0) :
    ∃ (x₀ y : T) (N : ℕ), x₀ ∈ P0 ∧ y ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀) ∧ s0 y = y ∧
      (∀ a b : S'.CornerRing i₀,
        ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y = 0 → a = 0 ∧ b = 0) ∧
      (∀ z ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀), ∃ a b : S'.CornerRing i₀,
        ((p : ℤ_[p]) ^ N) • z = ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y) ∧
      (∀ z ∈ P0, ∃ a : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z = ((a : S'.CornerRing i₀) : 𝕋) • x₀) ∧
      (∀ z ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀), s0 z = z →
        ∃ b : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z = ((b : S'.CornerRing i₀) : 𝕋) • y) :=
  OrdLat.core hfaith op hop hgen S' i₀ P0 s0 t1 u h2 hs0 ht1 hP0 hsq ht1P0 ht1unr b B hBnd hBself hBsim hu

end
end S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing
end P2MW
export P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing (solution)
