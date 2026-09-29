-- Prove2me | solution 1 for Function.exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/09c8d76a-713a-54b3-b66d-731174aafb8c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul

set_option autoImplicit false

namespace Function
p2m_export "Function" "update update_eq_iff update_of_ne update_self ne_iff support"
namespace SepFinAux
p2m_open "Function"

open Finset

theorem exists_points_eq_sum_apply_smul {X : Type} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (r : ℕ) (s : Fin r → X) (ℓ : Fin r → (X → ℂ)), (∀ j, ℓ j ∈ W) ∧ ∀ f ∈ W, f = ∑ j, f (s j) • ℓ j := by
  classical

  suffices H : ∀ n : ℕ, ∀ (W : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ W → Module.finrank ℂ W ≤ n →
      ∃ (r : ℕ) (s : Fin r → X) (ℓ : Fin r → (X → ℂ)), (∀ j, ℓ j ∈ W) ∧ ∀ f ∈ W, f = ∑ j, f (s j) • ℓ j from
    H _ W inferInstance le_rfl
  intro n
  induction n with
  | zero =>
    intro W _ hW
    have hbot : W = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hW)
    refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun f hf => ?_⟩
    rw [hbot, Submodule.mem_bot] at hf
    simp [hf]
  | succ n ih =>
    intro W _ hW
    by_cases hbot : W = ⊥
    · refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun f hf => ?_⟩
      rw [hbot, Submodule.mem_bot] at hf
      simp [hf]

    obtain ⟨f₀, hf₀W, hf₀⟩ := (Submodule.ne_bot_iff W).mp hbot
    obtain ⟨x, hx⟩ : ∃ x, f₀ x ≠ 0 := Function.ne_iff.mp hf₀

    let W' : Submodule ℂ (X → ℂ) := W ⊓ LinearMap.ker (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ)
    have hW'le : W' ≤ W := inf_le_left
    haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hW'le
    have hlt : W' < W := by
      refine lt_of_le_of_ne hW'le fun h => hx ?_
      have : f₀ ∈ W' := h ▸ hf₀W
      exact this.2
    have hrank : Module.finrank ℂ W' ≤ n := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    obtain ⟨r, s, ℓ, hℓ, hrep⟩ := ih W' inferInstance hrank

    let ℓ₀ : X → ℂ := (f₀ x)⁻¹ • f₀ - ∑ j, ((f₀ x)⁻¹ * f₀ (s j)) • ℓ j
    have hℓ₀ : ℓ₀ ∈ W :=
      W.sub_mem (W.smul_mem _ hf₀W) (W.sum_mem fun j _ => W.smul_mem _ (hW'le (hℓ j)))
    refine ⟨r + 1, Fin.cons x s, Fin.cons ℓ₀ ℓ, ?_, ?_⟩
    · refine Fin.cases ?_ ?_
      · simpa using hℓ₀
      · intro j; simpa using hW'le (hℓ j)
    · intro f hf
      set c : ℂ := f x * (f₀ x)⁻¹ with hc
      have hmem : f - c • f₀ ∈ W' := by
        refine ⟨W.sub_mem hf (W.smul_mem _ hf₀W), ?_⟩
        show (f - c • f₀) x = 0
        simp [hc, hx]
      have e1 := hrep _ hmem
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]

      have e2 : ∑ j, (f - c • f₀) (s j) • ℓ j = (∑ j, f (s j) • ℓ j) - c • ∑ j, f₀ (s j) • ℓ j := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum,
          smul_smul]
      have e3 : f x • ℓ₀ = c • f₀ - c • ∑ j, f₀ (s j) • ℓ j := by
        simp only [ℓ₀, smul_sub, smul_smul, Finset.smul_sum, hc, mul_assoc]
      rw [e3]
      rw [e2] at e1
      have e4 : f = c • f₀ + ((∑ j, f (s j) • ℓ j) - c • ∑ j, f₀ (s j) • ℓ j) := by
        rw [← e1]; abel
      refine e4.trans ?_
      abel

end Function.SepFinAux

namespace Function
p2m_export "Function" "update update_eq_iff update_of_ne update_self ne_iff support"
namespace SepFinAux
p2m_open "Function"

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}

omit [Fintype ι] in

theorem direction_step (Φ : (∀ j, X j) → ℂ) (i : ι)
    (h : ∃ (d : ℕ) (φ : Fin d → X i → ℂ), ∀ b : ∀ j, X j, ∃ c : Fin d → ℂ,
      ∀ t : X i, Φ (Function.update b i t) = ∑ k, c k * φ k t) :
    ∃ (B : Type) (_ : Fintype B) (sB : B → X i) (aB : B → ℂ) (bB : B → ∀ j, X j),
      ∀ (b : ∀ j, X j) (t : X i),
        Φ (Function.update b i t) = ∑ β, aB β * Φ (Function.update b i (sB β)) * Φ (Function.update (bB β) i t) := by
  classical
  obtain ⟨d, φ, hφ⟩ := h

  let P : (∀ j, X j) → (X i → ℂ) := fun b t => Φ (Function.update b i t)
  let W : Submodule ℂ (X i → ℂ) := Submodule.span ℂ (Set.range P)
  have hWle : W ≤ Submodule.span ℂ (Set.range φ) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    obtain ⟨c, hc⟩ := hφ b
    have hPb : P b = ∑ k, c k • φ k := by
      funext t
      simp only [P, hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hPb]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range φ)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range φ)
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWle

  obtain ⟨r, s, ℓ, hℓW, hrep⟩ := exists_points_eq_sum_apply_smul W
  have hcf : ∀ j, ∃ cj : (∀ j, X j) →₀ ℂ, (cj.sum fun b a => a • P b) = ℓ j := fun j =>
    Finsupp.mem_span_range_iff_exists_finsupp.mp (hℓW j)
  choose cf hcf using hcf
  refine ⟨(Σ j : Fin r, ((cf j).support : Type)), inferInstance, fun x => s x.1, fun x => cf x.1 x.2,
    fun x => (x.2 : ∀ j, X j), fun b t => ?_⟩

  have hPbW : P b ∈ W := Submodule.subset_span ⟨b, rfl⟩
  have e1 : Φ (Function.update b i t) = ∑ j, Φ (Function.update b i (s j)) * ℓ j t := by
    have := congrFun (hrep _ hPbW) t
    simpa only [P, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  have e2 : ∀ j, ℓ j t = ∑ b' ∈ (cf j).support, cf j b' * Φ (Function.update b' i t) := by
    intro j
    have := congrFun (hcf j) t
    rw [← this, Finsupp.sum, Finset.sum_apply]
    simp only [P, Pi.smul_apply, smul_eq_mul]
  rw [e1, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e2 j, Finset.mul_sum, ← Finset.sum_coe_sort (cf j).support]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

omit [Fintype ι] in

theorem main_induction (Φ : (∀ j, X j) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∃ (d : ℕ) (φ : Fin d → X i → ℂ), ∀ b : ∀ j, X j, ∃ c : Fin d → ℂ,
      ∀ t : X i, Φ (Function.update b i t) = ∑ k, c k * φ k t) :
    ∀ S : Finset ι, i₀ ∉ S →
      ∃ (A : Type) (_ : Fintype A) (coef : A → ℂ) (β : A → ι → ∀ j, X j) (γ : A → ∀ j, X j),
        ∀ t : ∀ j, X j, Φ t = ∑ a, coef a * ((∏ i ∈ S, Φ (Function.update (β a i) i (t i))) * Φ (S.piecewise (γ a) t)) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    by_cases hne : Nonempty (∀ j, X j)
    · refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => hne.some, fun _ => hne.some, fun t => ?_⟩
      simp
    · exact ⟨PEmpty, inferInstance, nofun, nofun, nofun, fun t => (hne ⟨t⟩).elim⟩
  | insert i S hiS ih =>
    intro hi₀
    have hii₀ : i ≠ i₀ := fun e => hi₀ (e ▸ Finset.mem_insert_self i S)
    have hi₀S : i₀ ∉ S := fun e => hi₀ (Finset.mem_insert_of_mem e)
    obtain ⟨A, _, coef, β, γ, hA⟩ := ih hi₀S
    obtain ⟨B, _, sB, aB, bB, hB⟩ := direction_step Φ i (h i hii₀)
    refine ⟨A × B, inferInstance, fun p => coef p.1 * aB p.2, fun p => Function.update (β p.1) i (bB p.2),
      fun p => Function.update (γ p.1) i (sB p.2), fun t => ?_⟩

    have key : ∀ a : A, Φ (S.piecewise (γ a) t) =
        ∑ b, aB b * Φ ((insert i S).piecewise (Function.update (γ a) i (sB b)) t) *
          Φ (Function.update (bB b) i (t i)) := by
      intro a
      have h0 : S.piecewise (γ a) t = Function.update (S.piecewise (γ a) t) i (t i) := by
        rw [eq_comm, Function.update_eq_iff]
        exact ⟨(Finset.piecewise_eq_of_notMem _ _ _ hiS).symm, fun _ _ => rfl⟩
      rw [h0, hB]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hpc : S.piecewise (Function.update (γ a) i (sB b)) t = S.piecewise (γ a) t := by
        funext j
        by_cases hj : j ∈ S
        · rw [Finset.piecewise_eq_of_mem _ _ _ hj, Finset.piecewise_eq_of_mem _ _ _ hj, Function.update_of_ne]
          rintro rfl; exact hiS hj
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hj, Finset.piecewise_eq_of_notMem _ _ _ hj]
      congr 2
      rw [Finset.piecewise_insert, Function.update_self, hpc]
    rw [hA t, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    have hprod : ∏ j ∈ S, Φ (Function.update (Function.update (β a) i (bB b) j) j (t j)) =
        ∏ j ∈ S, Φ (Function.update (β a j) j (t j)) :=
      Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hiS)]
    rw [Finset.prod_insert hiS, Function.update_self, hprod]
    ring

end Function.SepFinAux

open Function.SepFinAux in
theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Φ : (∀ i, X i) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∃ (d : ℕ) (φ : Fin d → X i → ℂ), ∀ b : ∀ j, X j, ∃ c : Fin d → ℂ,
      ∀ t : X i, Φ (Function.update b i t) = ∑ k, c k * φ k t) :
    ∃ (m : ℕ) (coef : Fin m → ℂ) (β : Fin m → ι → ∀ j, X j),
      ∀ t : ∀ j, X j, Φ t = ∑ α, coef α * ∏ i, Φ (Function.update (β α i) i (t i)) := by
  classical
  obtain ⟨A, _, coef, β, γ, hA⟩ := main_induction Φ i₀ h (Finset.univ.erase i₀) (Finset.notMem_erase i₀ _)
  let e := Fintype.equivFin A
  refine ⟨Fintype.card A, fun k => coef (e.symm k), fun k => Function.update (β (e.symm k)) i₀ (γ (e.symm k)),
    fun t => ?_⟩
  rw [hA t, ← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  have hpw : (Finset.univ.erase i₀).piecewise (γ (e.symm k)) t = Function.update (γ (e.symm k)) i₀ (t i₀) := by
    funext j
    by_cases hj : j = i₀
    · subst hj; rw [Function.update_self, Finset.piecewise_eq_of_notMem _ _ _ (Finset.notMem_erase j _)]
    · rw [Function.update_of_ne hj, Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)]
  have hprod : ∏ j ∈ Finset.univ.erase i₀, Φ (Function.update (Function.update (β (e.symm k)) i₀ (γ (e.symm k)) j) j (t j)) =
      ∏ j ∈ Finset.univ.erase i₀, Φ (Function.update (β (e.symm k) j) j (t j)) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), Function.update_self, hprod, hpw]
  ring

end S_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul
end P2MW
export P2MW.S_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul (solution)
