-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.gen_of_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:19.177989+00:00
-- url     : https://prove2.me/submissions/59f31659-2912-421d-b8e8-a4e3f98d82c8

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q] [Finite Q] (e : ℕ)
    (H : ∀ P : Ideal R, P.IsMaximal →
      ∃ s : Fin e → Q, Submodule.span R (Set.range s) ⊔ P • (⊤ : Submodule R Q) = ⊤) :
    ∃ s : Fin e → Q, Submodule.span R (Set.range s) = ⊤ := by
  classical
  let S : Set (Ideal R) := {P | P.IsMaximal ∧ P • (⊤ : Submodule R Q) ≠ ⊤}
  have hinj : Set.InjOn (fun P : Ideal R => P • (⊤ : Submodule R Q)) S := by
    intro P hP P' hP' hPP'
    by_contra hne
    have hsup : P ⊔ P' = ⊤ := hP.1.coprime_of_ne hP'.1 hne
    apply hP.2
    have hPP'' : P • (⊤ : Submodule R Q) = P' • (⊤ : Submodule R Q) := hPP'
    have h1 : (P ⊔ P') • (⊤ : Submodule R Q) = P • (⊤ : Submodule R Q) := by
      rw [Submodule.sup_smul, ← hPP'', sup_idem]
    rw [← h1, hsup, Submodule.top_smul]
  have hfin : S.Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  have : Finite S := hfin
  let _ := Fintype.ofFinite S
  choose! sP hsP using H
  have hcop : Pairwise (Function.onFun IsCoprime (fun i : S => (i : Ideal R))) := by
    intro i j hij
    show IsCoprime (i : Ideal R) (j : Ideal R)
    rw [Ideal.isCoprime_iff_sup_eq]
    exact i.2.1.coprime_of_ne j.2.1 (fun h => hij (Subtype.ext h))
  have hε : ∀ i : S, ∃ r : R, ∀ j : S, r - (if j = i then 1 else 0) ∈ (j : Ideal R) :=
    fun i => Ideal.exists_forall_sub_mem_ideal hcop _
  choose ε hε using hε
  let s : Fin e → Q := fun k => ∑ i : S, ε i • sP i k
  refine ⟨s, ?_⟩
  by_contra hne
  obtain ⟨N', hN', hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hne
  have hsimple : IsSimpleModule R (Q ⧸ N') := isSimpleModule_iff_isCoatom.mpr hN'
  obtain ⟨P, hPmax, ⟨f⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  have hPN : P • (⊤ : Submodule R Q) ≤ N' := by
    rw [Submodule.smul_le]
    intro r hr x _
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    apply f.injective
    rw [map_smul, map_zero]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (f (Submodule.Quotient.mk x))
    rw [← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact P.mul_mem_right y hr
  have hPS : P ∈ S := ⟨hPmax, fun h => hN'.1 (top_le_iff.mp (h ▸ hPN))⟩
  have hk : ∀ k, sP P k ∈ N' := by
    intro k
    have h1 : s k - sP P k ∈ P • (⊤ : Submodule R Q) := by
      have h2 : sP P k = ∑ i : S, (if (⟨P, hPS⟩ : S) = i then (1 : R) else 0) • sP i k := by
        simp [ite_smul]
      have h3 : s k - sP P k =
          ∑ i : S, (ε i - (if (⟨P, hPS⟩ : S) = i then (1 : R) else 0)) • sP i k := by
        conv_lhs => rw [h2]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
      rw [h3]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hε i ⟨P, hPS⟩) trivial
    have h4 : s k ∈ N' := hle (Submodule.subset_span ⟨k, rfl⟩)
    have h5 : sP P k = s k - (s k - sP P k) := by abel
    rw [h5]
    exact N'.sub_mem h4 (hPN h1)
  have h6 : Submodule.span R (Set.range (sP P)) ⊔ P • (⊤ : Submodule R Q) ≤ N' := by
    refine sup_le ?_ hPN
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hk k
  rw [hsP P hPmax] at h6
  exact hN'.1 (top_le_iff.mp h6)
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
