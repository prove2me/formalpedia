-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.finrank_span_cols_union_single
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:37:04.678348+00:00
-- url     : https://prove2.me/submissions/09b7993b-95d9-4d69-9fe2-6802f8a3443b

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

set_option autoImplicit false

namespace DiscreteConvex.MixedMatrices

/-- Dimension of the span of the columns `M_c` (`c ∈ J`) together with the unit vectors `e_s`
(`s ∈ N`): it is `|N|` plus the rank of the submatrix `M[R \ N, J]`. -/
theorem pk_finrank_span_cols_union_single {R C F : Type*} [Fintype R] [Fintype C] [Field F]
    [DecidableEq R] (M : Matrix R C F) (J : Finset C) (N : Finset R) :
    Module.finrank F (Submodule.span F
      (((fun c : C => (fun r : R => M r c)) '' (J : Set C)) ∪
        ((fun s : R => (Pi.single s (1 : F) : R → F)) '' (N : Set R)))) =
      N.card + MatrixSubRank M Nᶜ J := by
  classical
  -- restriction to the rows outside `N`
  let π : (R → F) →ₗ[F] ({x // x ∈ Nᶜ} → F) := LinearMap.funLeft F F (Subtype.val)
  let E : Submodule F (R → F) :=
    Submodule.span F ((fun s : R => (Pi.single s (1 : F) : R → F)) '' (N : Set R))
  let W : Submodule F (R → F) := Submodule.span F
      (((fun c : C => (fun r : R => M r c)) '' (J : Set C)) ∪
        ((fun s : R => (Pi.single s (1 : F) : R → F)) '' (N : Set R)))
  have hπe : ∀ s ∈ N, π (Pi.single s (1 : F)) = 0 := by
    intro s hs
    ext x
    have : (x : R) ≠ s := fun h => (Finset.mem_compl.mp x.2) (h ▸ hs)
    simp [π, this]
  -- the kernel of `π` is exactly `E`
  have hker : LinearMap.ker π = E := by
    apply le_antisymm
    · intro f hf
      have hf0 : ∀ x : R, x ∉ N → f x = 0 := by
        intro x hx
        have := congrFun hf ⟨x, Finset.mem_compl.mpr hx⟩
        simpa [π] using this
      have : f = ∑ s ∈ N, f s • (Pi.single s (1 : F) : R → F) := by
        ext x
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero]
        by_cases hx : x ∈ N
        · rw [Finset.sum_ite_eq N x]; simp [hx]
        · rw [Finset.sum_ite_eq N x]; simp [hx, hf0 x hx]
      rw [this]
      exact Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨s, hs, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨s, hs, rfl⟩
      exact hπe s hs
  have hEW : E ≤ W := Submodule.span_mono Set.subset_union_right
  -- the dimension of `E`
  have hdimE : Module.finrank F E = N.card := by
    have hli : LinearIndependent F (fun s : N => (Pi.single (s : R) (1 : F) : R → F)) := by
      have h := (Pi.basisFun F R).linearIndependent.comp (fun s : N => (s : R)) Subtype.val_injective
      have heq : (⇑(Pi.basisFun F R) ∘ fun s : N => (s : R)) =
          fun s : N => (Pi.single (s : R) (1 : F) : R → F) := by
        funext s
        simp [Pi.basisFun_apply]
      rwa [heq] at h
    have h := finrank_span_eq_card hli
    have hrange : Set.range (fun s : N => (Pi.single (s : R) (1 : F) : R → F)) =
        (fun s : R => (Pi.single s (1 : F) : R → F)) '' (N : Set R) := by
      ext v
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨s, s.2, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hs⟩, rfl⟩
    rw [hrange] at h
    simpa using h
  -- the image of `W` under `π`
  have hEmap : E.map π = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨v, hv, rfl⟩
    have : v ∈ LinearMap.ker π := hker ▸ hv
    simpa using this
  have hmap : W.map π = Submodule.span F (Set.range
      (M.submatrix ((↑) : (Nᶜ : Finset R) → R) ((↑) : J → C)).col) := by
    have h1 : W = Submodule.span F ((fun c : C => (fun r : R => M r c)) '' (J : Set C)) ⊔ E := by
      rw [← Submodule.span_union]
    rw [h1, Submodule.map_sup, hEmap, sup_bot_eq, Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, ⟨c, c.2, rfl⟩, rfl⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker (π.domRestrict W)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, hmap] at hrk
  have hkerE : Module.finrank F ((LinearMap.ker π).comap W.subtype) = N.card := by
    rw [(Submodule.comapSubtypeEquivOfLe (hker ▸ hEW)).finrank_eq, hker, hdimE]
  rw [hkerE, ← Matrix.rank_eq_finrank_span_cols] at hrk
  unfold MatrixSubRank
  show Module.finrank F W = _
  omega

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices

theorem solution {R C F : Type*} [Fintype R] [Fintype C] [Field F]
    [DecidableEq R] (M : Matrix R C F) (J : Finset C) (N : Finset R) :
    Module.finrank F (Submodule.span F
      (((fun c : C => (fun r : R => M r c)) '' (J : Set C)) ∪
        ((fun s : R => (Pi.single s (1 : F) : R → F)) '' (N : Set R)))) =
      N.card + MatrixSubRank M Nᶜ J :=
  pk_finrank_span_cols_union_single M J N

#print axioms solution
