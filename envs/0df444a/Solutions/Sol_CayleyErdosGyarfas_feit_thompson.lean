-- Prove2me | solution 1 for CayleyErdosGyarfas.feit_thompson
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T18:05:54.064975+00:00
-- url     : https://prove2.me/submissions/4dbdc675-c553-4c24-899d-b44691dd8b28

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ClassFunction.lean
--   OddOrder/GroupTheory/TISubset.lean
--   OddOrder/Peterfalvi/S05_TICyclic.lean
--   OddOrder/Peterfalvi/S06_CertainTypeCharacters.lean
--   OddOrder/Peterfalvi/S05_IntegralSigma.lean
--   OddOrder/Peterfalvi/S10_Theorem88CaseB.lean
--   OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean
--   OddOrder/Peterfalvi/S06_MuColumnBridge.lean
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/FeitThompsonSection16Core.lean
--   OddOrder/FeitThompsonSetup.lean
--   OddOrder/FeitThompsonNuGrid.lean
--   OddOrder/FeitThompsonPairProducer.lean
--   OddOrder/FeitThompsonCharacterData.lean
--   OddOrder/FeitThompson.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Theorems.Thm_OddOrder_BG_Ch4_S14_exists_kappaHall_invariant_complement_to_MF
import Theorems.Thm_OddOrder_Section16CharacterData_tau3W_omegaS_pair_of_coprime
import Theorems.Thm_OddOrder_Section16CharacterData_tau3W_omegaS_fourcorner_vanish
import Theorems.Thm_OddOrder_Section16CharacterData_nuT_reducible_dichotomy
import Theorems.Thm_OddOrder_noMinimalSimpleOdd_of_section16
import Theorems.Thm_OddOrder_exists_section16MaximalPair_data
import Theorems.Thm_OddOrder_Section16CharacterData_muS_reducible_dichotomy

-- ===== OddOrder/GroupTheory/RepresentationTheory/ClassFunction.lean =====
namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

section CompHom

variable {G : Type*} [Group G] {H : Type*} [Group H] {k : Type*} [CommRing k]

theorem compHom_sub (f : H →* G) (φ ψ : ClassFunction G k) :
    compHom f (φ - ψ) = compHom f φ - compHom f ψ := by ext h; simp

end CompHom

section Inner

variable {G : Type*} [Group G] [Fintype G]

variable {k : Type*} [CommRing k] [StarRing k]

/-- The unscaled inner sum is invariant under pullback along a group **isomorphism**:
reindexing the sum over `H` by `e : H ≃* G` recovers the sum over `G`. -/
theorem innerSum_compHom_mulEquiv {H : Type*} [Group H] [Fintype H] (e : H ≃* G)
    (φ ψ : ClassFunction G k) :
    innerSum (compHom e.toMonoidHom φ) (compHom e.toMonoidHom ψ) = innerSum φ ψ := by
  simpa [innerSum] using e.toEquiv.sum_comp (fun g => φ g * star (ψ g))

/-- The normalized inner product is invariant under pullback along a group isomorphism
(`|H| = |G|`, so the normalizations agree). -/
theorem inner_compHom_mulEquiv {H : Type*} [Group H] [Fintype H] (e : H ≃* G)
    [Invertible (Nat.card H : k)] [Invertible (Nat.card G : k)]
    (φ ψ : ClassFunction G k) :
    inner (compHom e.toMonoidHom φ) (compHom e.toMonoidHom ψ) = inner φ ψ := by
  have hcard : ((Nat.card H : ℕ) : k) = ((Nat.card G : ℕ) : k) := by
    rw [Nat.card_congr e.toEquiv]
  have h := innerSum_compHom_mulEquiv e φ ψ
  calc inner (compHom e.toMonoidHom φ) (compHom e.toMonoidHom ψ)
      = ⅟(Nat.card H : k) * innerSum φ ψ := by rw [inner, h]
    _ = ⅟(Nat.card H : k) * ((Nat.card H : k) * inner φ ψ) := by
        rw [← card_mul_inner, ← hcard]
    _ = inner φ ψ := by rw [← mul_assoc, invOf_mul_self, one_mul]

end Inner

end ClassFunction

end OddOrder.RepresentationTheory

-- ===== OddOrder/GroupTheory/TISubset.lean =====
namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

namespace IsTISubset

variable {A : Set G} {L : Subgroup G}

/-- **A TI-subset inside an abelian host pins the normalizer of each of its nonempty pieces**:
if `A` is a TI-subset with normalizer-bound `L`, `A` sits inside `L`, and `L` is commutative,
then `N_G(X) = L` for *every* nonempty `X ⊆ A`.

Both inclusions are short.  For `N_G(X) ≤ L`, pick any `a ∈ X`; then `g·a·g⁻¹ ∈ X ⊆ A`, so the
TI condition places `g ∈ L`.  For `L ≤ N_G(X)`, conjugation by `w ∈ L` fixes every element of
`L` — and both `h ∈ X ⊆ L` and (in the converse direction) `h = w⁻¹·(w·h·w⁻¹)·w ∈ L` — so the
membership iff is an identity.

This is the abstract content of Peterfalvi (8.4.e) (`N_G(X) = W` for every nonempty
`X ⊆ W − (W₁ ∪ W₂)`): BG Theorem 14.7 delivers exactly `IsTISubset (zTilde K K*) (K ⊔ K*)`
together with the cyclicity of `K ⊔ K*`, and (8.4.e) is this lemma applied to them. -/
theorem set_normalizer_eq_of_subset_of_commute (hA : IsTISubset A L) (hAL : A ⊆ (L : Set G))
    (hcomm : ∀ x ∈ L, ∀ y ∈ L, Commute x y)
    {X : Set G} (hX : X.Nonempty) (hXA : X ⊆ A) :
    Subgroup.normalizer X = L := by
  -- Conjugation by an element of `L` fixes `L` pointwise.
  have hfix : ∀ w ∈ L, ∀ h ∈ L, w * h * w⁻¹ = h := by
    intro w hw h hh
    rw [(hcomm w hw h hh).eq, mul_inv_cancel_right]
  refine le_antisymm (fun g hg => ?_) (fun w hw => ?_)
  · obtain ⟨a, ha⟩ := hX
    exact hA g ⟨a, hXA ha, hXA ((Subgroup.mem_set_normalizer_iff.mp hg a).mp ha)⟩
  · rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh; rwa [hfix w hw h (hAL (hXA hh))]
    · intro hh
      -- `h` is a priori arbitrary, but `w·h·w⁻¹ ∈ X ⊆ L` forces `h ∈ L`.
      have hhL : h ∈ L := by
        have : w⁻¹ * (w * h * w⁻¹) * w ∈ L :=
          mul_mem (mul_mem (inv_mem hw) (hAL (hXA hh))) hw
        simpa [mul_assoc] using this
      rwa [hfix w hw h hhL] at hh

end IsTISubset

end OddOrder.GroupTheory

-- ===== OddOrder/Peterfalvi/S05_TICyclic.lean =====
namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

open scoped Classical in
/-- The `ω`-family orthonormality in Kronecker form: `⟨ω(χ), ω(χ')⟩ = δ_{χχ'}`
(`omega_inner_self` + `omega_inner_ne` combined; the shape the §13 grid fields carry). -/
theorem omega_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] (χ χ' : hyp.W →* ℂˣ) :
    ClassFunction.inner (hyp.omega χ : ClassFunction hyp.W ℂ)
      (hyp.omega χ' : ClassFunction hyp.W ℂ) = if χ = χ' then 1 else 0 := by
  split_ifs with h
  · subst h; exact hyp.omega_inner_self χ
  · exact hyp.omega_inner_ne h

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05

-- ===== OddOrder/Peterfalvi/S06_CertainTypeCharacters.lean =====
namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S05

variable {L : Type*} [Group L] [Fintype L]

section CyclicPowEnum

variable (D : Type*) [Group D] [Finite D] [IsCyclic D]

variable {D} {n : ℕ}

/-- The power enumeration pairs indices summing to `0 (mod n)` into inverse elements — the
abstract form of "index negation = inversion". -/
theorem cyclicPowEnum_eq_inv_of_add_mod_eq_zero (hn : Nat.card D = n) {i j : Fin n}
    (hij : ((i : ℕ) + (j : ℕ)) % n = 0) :
    cyclicPowEnum hn i = (cyclicPowEnum hn j)⁻¹ := by
  have hord : orderOf (cyclicGenerator D) = n := (orderOf_cyclicGenerator D).trans hn
  have key : cyclicPowEnum hn i * cyclicPowEnum hn j = 1 := by
    change cyclicGenerator D ^ (i : ℕ) * cyclicGenerator D ^ (j : ℕ) = 1
    rw [← pow_add, ← pow_mod_orderOf, hord, hij, pow_zero]
  exact mul_eq_one_iff_eq_inv.mp key

end CyclicPowEnum

namespace Hypothesis

variable (h : Hypothesis L)

/-- **Index negation is character inversion** (Peterfalvi (3.5)/(3.9.a) power-grid pairing):
`w1CharEquiv ((w₁ − i) % w₁) = (w1CharEquiv i)⁻¹`.  The `(3.9.a)` `finNeg`-pairing of the
`η`-grid is honest precisely because the enumeration satisfies this. -/
theorem w1CharEquiv_finNeg [NeZero (Nat.card h.W1)] (i : Fin (Nat.card h.W1)) :
    h.w1CharEquiv ⟨(Nat.card h.W1 - (i : ℕ)) % Nat.card h.W1,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩
      = (h.w1CharEquiv i)⁻¹ := by
  have := h.isCyclic_w1CharGroup
  rw [w1CharEquiv]
  refine cyclicPowEnum_eq_inv_of_add_mod_eq_zero _ ?_
  change ((Nat.card h.W1 - (i : ℕ)) % Nat.card h.W1 + (i : ℕ)) % Nat.card h.W1 = 0
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · simp [h0]
  · have hi : (i : ℕ) < Nat.card h.W1 := i.2
    rw [Nat.mod_eq_of_lt (by omega : Nat.card h.W1 - (i : ℕ) < Nat.card h.W1),
      Nat.sub_add_cancel hi.le, Nat.mod_self]

end Hypothesis

end OddOrder.Peterfalvi.S06

-- ===== OddOrder/Peterfalvi/S05_IntegralSigma.lean =====
namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

variable (hyp : TICyclicHypothesis G) [Fintype hyp.W]
  [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
  (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)

/-- The integral (3.2) map is an integral isometry (Peterfalvi (3.2), isometry
part). -/
theorem sigmaIntegral_isIntegralIsometry :
    OddOrder.Peterfalvi.S07.IsIntegralIsometry (hyp.sigmaIntegral hVeq app) :=
  ⟨fun φ ψ => hyp.sigma_inner hVeq app φ ψ⟩

/-- The integral (3.2) map sends the trivial character of `W` to that of `G`. -/
theorem sigmaIntegral_trivial :
    hyp.sigmaIntegral hVeq app (trivialClassFunction hyp.W) = trivialClassFunction G :=
  hyp.sigma_trivial hVeq app

/-- The integral (3.2) map sends virtual characters to virtual characters. -/
theorem sigmaIntegral_mem_ZIrr {z : ClassFunction hyp.W ℂ} (hz : z ∈ ZIrr hyp.W) :
    hyp.sigmaIntegral hVeq app z ∈ ZIrr G :=
  hyp.sigma_mem_ZIrr hVeq app hz

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05

-- ===== OddOrder/Peterfalvi/S10_Theorem88CaseB.lean =====
namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **(8.4.e) from the BG §14 TI-set** — the route both producers of `Theorem88CaseBData` use.

BG Theorem 14.7 (`typeP_duality`) hands out two facts about the κ-Hall pair `K`, `K*` of a
type-`P` maximal subgroup: the join `K ⊔ K*` is cyclic, and `Ẑ = (K ⊔ K*) − (K ∪ K*)`
(`OddOrder.BG.Ch4.S14.zTilde`, definitionally the set below) is a TI-subset with
normalizer-bound `K ⊔ K*`.  Together these *are* (8.4.e): a cyclic host is commutative, so
`set_normalizer_eq_of_subset_of_commute` applies.

Note that neither conjunct mentions the dual maximal subgroup, so a producer holding only the
pair `(K, K*)` can supply (8.4.e) without identifying the `∃!` partner — and without a
`TypePData` carrier (which would additionally demand type-`P₂`-ness and a `K`-invariant
`(κ∪σ)′`-Hall complement). -/
theorem normalizer_V_of_isTISubset {A B : Subgroup G} (hcyc : IsCyclic ↥(A ⊔ B))
    (hTI : IsTISubset (((A ⊔ B : Subgroup G) : Set G) \ ((A : Set G) ∪ (B : Set G))) (A ⊔ B)) :
    ∀ X : Set G, X.Nonempty →
      X ⊆ ((A ⊔ B : Subgroup G) : Set G) \ ((A : Set G) ∪ (B : Set G)) →
      Subgroup.normalizer X = A ⊔ B := by
  have := hcyc
  let : CommGroup ↥(A ⊔ B) := IsCyclic.commGroup
  refine fun X hX hXV => hTI.set_normalizer_eq_of_subset_of_commute Set.sdiff_subset ?_ hX hXV
  exact fun x hx y hy => congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(A ⊔ B)) ⟨y, hy⟩)

end OddOrder.Peterfalvi.S10

-- ===== OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean =====
namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- A non-type-I maximal subgroup that is not of type V (so of type II/III/IV) carries type-`P`
data whose `W₁` has prime order — Peterfalvi (8.6.a), via `TypePNontrivialCore`.  Type V is
excluded by the (10.10) hypothesis `hnoV` (supplied downstream by the axiom-clean
`no_typeV_maximal_unconditional`, `S12_Noncoherence`; issue 9087). -/
private theorem caseB_typeP_prime_W1 [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hnonI : IsTypeNonI M) :
    ∃ data : TypePData M, (Nat.card ↥data.W1).Prime := by
  rcases hnonI with h | h | h | h
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact absurd ⟨M, hM, h⟩ hnoV

/-- **Peterfalvi (10.11), first assertion**: in case (b) of Theorem (8.8), the
orders of `W_1` and `W_2` are prime.

By the (10.10) hypothesis `hnoV` (Type-V exclusion; instantiate with the axiom-clean
`no_typeV_maximal_unconditional`, `S12_Noncoherence`), the non-type-I subgroups `S`, `T` are of
type II/III/IV, whose type-`P` `W₁` has prime order (8.6.a).  The case-(b) factors `W₁`, `W₂`
complement the derived subgroups of `S`, `T` (8.8.b1, `S_compl`/`T_compl`), so they share the
orders `|S : S'|`, `|T : T'|` with the respective type-`P` `W₁` (`card_W1_eq_derived_index`)
— hence prime. -/
theorem theorem88_caseB_prime_orders [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (caseB : S10.Theorem88CaseBData G) :
    (Nat.card ↥caseB.W1).Prime ∧ (Nat.card ↥caseB.W2).Prime := by
  have hW1 : Nat.card ↥caseB.W1 = ((derivedInG caseB.S).subgroupOf caseB.S).index := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe caseB.W1_le_S).toEquiv,
      ← caseB.S_compl.symm.index_eq_card]
  have hW2 : Nat.card ↥caseB.W2 = ((derivedInG caseB.T).subgroupOf caseB.T).index := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe caseB.W2_le_T).toEquiv,
      ← caseB.T_compl.symm.index_eq_card]
  refine ⟨?_, ?_⟩
  · obtain ⟨dataS, hSp⟩ := caseB_typeP_prime_W1 hG hnoV caseB.S_maximal caseB.S_nonI
    rw [hW1, ← dataS.card_W1_eq_derived_index]; exact hSp
  · obtain ⟨dataT, hTp⟩ := caseB_typeP_prime_W1 hG hnoV caseB.T_maximal caseB.T_nonI
    rw [hW2, ← dataT.card_W1_eq_derived_index]; exact hTp

end OddOrder.Peterfalvi.S12

-- ===== OddOrder/Peterfalvi/S06_MuColumnBridge.lean =====
namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S05

namespace Hypothesis

/-- **Peterfalvi (13.1.e), per `W₂`-column, explicit `μ`-difference form** (endpoint D).
For a certain-type hypothesis `h` and a `W₂`-dual `χ₂`, the (4.3.b) certain-type
characters satisfy `Ind_W^L(ω_{iχ₂} − ω_{0χ₂}) = δ_{χ₂} (μ_{iχ₂} − μ_{0χ₂})`.  Direct
from `induce_omegaColumnDiff_eq` once the signed difference is written out. -/
theorem induce_omegaColumnDiff_mu_diff {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : Hypothesis L) [NeZero (Nat.card h.W1)]
    [Finite (h.W1 ⊔ h.W2 : Subgroup L)]
    [Invertible (Nat.card (h.W1 ⊔ h.W2 : Subgroup L) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.induce h.sdiffTICyclicHypothesis.W
        (h.omegaColumnDiff (h.w1CharEquiv i) 1 χ₂ :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.columnFamily χ₂).sign •
          ((h.columnFamily χ₂).classFunction i - (h.columnFamily χ₂).classFunction 0) := by
  have : Fintype (h.W1 ⊔ h.W2 : Subgroup L) := Fintype.ofFinite _
  rw [h.induce_omegaColumnDiff_eq χ₂ (h.w1CharEquiv i), Equiv.symm_apply_apply]

/-- **Peterfalvi (13.1.e), the `ω`/`μ`-grid difference form** — the exact shape consumed by the
§13 character grids (`Section16CharacterData.mu_definition` / `S15.Hypothesis.mu_definition`).

Inducing the `W₂`-column `ω`-grid difference `ω_{ij} − ω_{0j}` of the certain-type
`W = W₁ ⊔ W₂` up to `L` yields the signed `μ`-grid difference `δ_j (μ_{ij} − μ_{0j})`, where the
`ω`-grid is the column `i ↦ chiColumn χ₂ i = ω(omegaProdChar (e i) χ₂)` and the `μ`-grid is the
`(4.3.b)` certain-type family `columnFamily χ₂ |>.mu`.  This restates
`induce_omegaColumnDiff_mu_diff` with the `chiColumn`-difference on the left and the irreducible
`μ_{ij}` (not the abstract `classFunction`) on the right — the literal `Ind_W^S(ω_{ij} − ω_{0j}) =
δ_j(μ_{ij} − μ_{0j})` of (13.1.e), so a §13/§16 grid producer reading off `ω`/`μ`/`δ` from a
certain-type member can discharge `mu_definition` by this lemma plus the column reindexing. -/
theorem induce_chiColumn_diff_mu_diff {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : Hypothesis L) [NeZero (Nat.card h.W1)]
    [Finite (h.W1 ⊔ h.W2 : Subgroup L)]
    [Invertible (Nat.card (h.W1 ⊔ h.W2 : Subgroup L) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.induce h.sdiffTICyclicHypothesis.W
        ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ))
      = (h.columnFamily χ₂).sign •
          (((h.columnFamily χ₂).mu i : ClassFunction L ℂ)
            - ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)) := by
  have : Fintype (h.W1 ⊔ h.W2 : Subgroup L) := Fintype.ofFinite _
  have hchi : (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.omegaColumnDiff (h.w1CharEquiv i) 1 χ₂ :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ) := by
    rw [h.omegaColumnDiff_coe, h.chiColumn_zero]
    rfl
  rw [hchi, h.induce_omegaColumnDiff_mu_diff χ₂ i,
    SignedIrreducibleDifferenceFamily.classFunction_apply,
    SignedIrreducibleDifferenceFamily.classFunction_apply]

end Hypothesis

end OddOrder.Peterfalvi.S06

-- ===== OddOrder/Peterfalvi/S13_TypeDetermination.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

/-- **Peterfalvi (11.9.b), character core** (Peterfalvi §11
coherence / Dade norm).  For a Type III/IV maximal subgroup `S` (the Hypothesis (11.2) case), with
κ-Hall factor `K` and dual factor `K* = M_σ(S) ⊓ C_G(K)`, the coherence / norm-inequality bound on
the character set `S(HC)` forces `q > p`, i.e. the dual factor is the smaller: `|K*| < |K|`
(`q = |W₁| = |K|`, `p = |W₂| = |K*|`).

The proof is now **fully assembled** from three pieces: (i) the carrier translation `|K| = w₁` (both
`K` and `W₁` complement `M'`, so both equal the derived index — `card_kappaHall_eq_derived_index`,
`TypePData.card_W1_eq_derived_index`); (ii) the carrier translation `|K*| = w₂`
(`card_Msigma_inf_centralizer_eq_card_W2`, axiom-clean BG §14 group theory); and (iii) the §11
character reduction `w₂ < w₁` (`S13.w2_lt_w1_of_hypothesis_H0C_unconditional` — the honest
narrow-`𝒮(H₀C)` route on the unconditional (11.3), issues 1019/1020; the deprecated wide
`S12.w2_lt_w1_of_hypothesis` and its false uniform-degree lemma have been retired).  All of
(i)/(ii) and the reduction spine of (iii) are proven; the residual is the genuine Peterfalvi
(11.8) non-orthogonality (`S13.exists_zeta_residual_not_orthogonal_H0C_of_refuter`), which
rests on the §14 Sibley glue `(6.7)`/`(5.8)` and the `(9.11)` caseA refuter (the `(10.8)`
residual is discharged by `S_not_coherent_unconditional`).  All of these are now proved. -/
theorem card_kappaHall_lt_of_isTypeIIIorIV {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hIIIorIV : IsTypeIII S ∨ IsTypeIV S) :
    Nat.card ↥Kstar < Nat.card ↥K := by
  -- `K` is cyclic, as a subgroup of the cyclic `Z = K ⊔ K*` (BG 14.7(d), via `typeP_duality`).
  obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
    BG.Ch4.S14.typeP_duality hG hS hSP hKS hK hKstar
  have : IsCyclic ↥(K ⊔ Kstar) := hcyc
  have : IsCyclic ↥K :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Kstar))
      (Subgroup.inclusion_injective _)
  -- Build the §10 hypothesis on `S` (type III/IV ⊆ III/IV/V).
  obtain ⟨hyp⟩ := OddOrder.Peterfalvi.S12.exists_hypothesis_of_typeIIIorIVorV hG hS
    (hIIIorIV.imp id Or.inl)
  -- `|K| = w₁`: both `K` and `W₁` complement `M'`, so both equal the derived index.
  have hKw1 : Nat.card ↥K = hyp.w1 := by
    rw [BG.Ch4.S16.card_kappaHall_eq_derived_index hG hS hSP hKS hK]
    exact hyp.typeP.card_W1_eq_derived_index.symm
  -- `|K*| = w₂`: the carrier bridge (lane-b W3, BG §14 group theory, now in `S10`).
  have hKstarw2 : Nat.card ↥Kstar = hyp.w2 := by
    rw [hKstar]
    exact OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2 hG hS hSP hKS hK hyp.typeP
  -- The two (11.5)/(11.7) structural facts, discharged via §13 (`secondDerived_eq_HC`,
  -- `H_elementaryAbelian`): `M'' = H ⊔ C_U(H)` and `|H| = |W₂|^{|W₁|}`.
  have hM2 : secondDerivedInAmbient S
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)) :=
    OddOrder.Peterfalvi.S13.secondDerived_eq_fitting_of_base hG hyp hIIIorIV
      (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
  have hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1 :=
    OddOrder.Peterfalvi.S13.card_H_eq_of_base hG hyp hIIIorIV
      (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
  -- `w₂ < w₁` (Peterfalvi (11.9.b), from the genuine (11.8) via the honest narrow `𝒮(H₀C)` route
  -- on the unconditional (11.3) — `w2_lt_w1_of_hypothesis_H0C_unconditional`, issues 1019/1020).
  rw [hKstarw2, hKw1]
  exact OddOrder.Peterfalvi.S13.w2_lt_w1_of_hypothesis_H0C_unconditional hG hyp hIIIorIV hM2
    hHcard

/-- **Peterfalvi (13.2.a), character core** (mmd §13, `references/peterfalvi/04.15_*`).

For the type-`P` member `S` of a dual maximal pair (BG Theorem 14.7), with κ-Hall factor `K` and
dual factor `K* = M_σ(S) ⊓ C_G(K)`, the type-`P₁` alternative (`S` of Type III/IV/V) carries the
*larger* κ-Hall factor: `|K*| < |K|`.  In Peterfalvi's notation `q = |W₁| = |K|`, `p = |W₂| = |K*|`,
this is "`S` of Type III ⟹ `q > p`".

**Type-V exclusion via the unconditional Theorem (10.10)** (issue 1020 Phase 3 relayering): by
the type dictionary `proposition_type_classification`, a type-`P₁` `S` is Type III/IV (if
`M_F ≠ M_σ`) or Type V (if `M_F = M_σ`); the latter is impossible by
`no_typeV_maximal_unconditional` (`S12_Noncoherence` — the honest (10.8) → (10.10) chain,
including the (6.5) gate lemmas of issue 2022), so `S` is Type III/IV and the
genuinely §11 character core `card_kappaHall_lt_of_isTypeIIIorIV` ((11.9.b)) applies.  Consumed
by `isTypeP2_of_typeP_kappaHall_lt`. -/
theorem card_kappaHall_lt_of_isTypeP1 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hP1 : BG.Ch4.S14.IsTypeP1 S) :
    Nat.card ↥Kstar < Nat.card ↥K := by
  -- Type dictionary: `S` type-`P₁` ⟹ Type III/IV (`M_F ≠ M_σ`) or Type V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ := BG.Ch4.S16.proposition_type_classification hG hS
  -- Type V is excluded by Theorem (10.10) `no_typeV_maximal`, so `M_F ≠ M_σ` and `S` is III/IV.
  have hMF : BG.Ch4.S15.MF S ≠ BG.Ch3.S10.Msigma S := fun hMF =>
    OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG ⟨S, hS, hdV.mpr ⟨hP1, hMF⟩⟩
  -- The genuinely §11 character core (11.9.b) gives `|K*| < |K|`.
  exact card_kappaHall_lt_of_isTypeIIIorIV hG hS hSP hKS hK hKstar (hcIII_IV.mpr ⟨hP1, hMF⟩)

/-- **Peterfalvi (13.2.a)** (mmd §13, `references/peterfalvi/04.15_*`): the type-`P` member `S` of a
dual maximal pair whose κ-Hall factor `K` is the *smaller* of the two coprime factors of
`W = K × K*` is of type `P₂` (BG) / Type II (Peterfalvi).

This selects, out of the type-duality disjunction `IsTypeP2 S ∨ IsTypeP2 T` (BG Theorem 14.7,
`typeP_duality`, which carries no order information), the determinate side `IsTypeP2 S` fixed by the
ordering `|K| < |K*|`.  Skeleton proof: `S` is type-`P`, hence type `P₁` or `P₂`
(`isTypeP_iff_isTypeP1_or_isTypeP2`); the `P₁` branch is excluded by `card_kappaHall_lt_of_isTypeP1`
(the Pf §10–§11 character core), leaving `P₂`.

Consumed by `section16MaximalPair_of_isMinimalSimpleOdd` to carry `Section16MaximalPair.S_typeP2`
(relane #4, issues 4009/2019), which unblocks the §15 `basic_structure` `TypePData` carrier wiring
(`exists_typePData_W1_eq_of_isTypeP2`). -/
theorem isTypeP2_of_typeP_kappaHall_lt {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hlt : Nat.card ↥K < Nat.card ↥Kstar) :
    BG.Ch4.S14.IsTypeP2 S := by
  rcases BG.Ch4.S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hSP with hP1 | hP2
  · exact absurd (card_kappaHall_lt_of_isTypeP1 hG hS hSP hKS hK hKstar hP1) (lt_asymm hlt)
  · exact hP2

end OddOrder

-- ===== OddOrder/FeitThompsonSection16Core.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

/-- **Named inputs for the Peterfalvi Section 16 configuration** (gated-endpoint
skeleton).

This bundles the genuine upstream witnesses that the Bender–Glauberman local
analysis (BG §7–§16) and Peterfalvi's character theory (Peterfalvi §3–§16) must
construct in order to enter Section 16.  It is `Peterfalvi.S15.Hypothesis`
together with the standing inequality `q < p` of (14.1), *minus* the fields that
`sectionSixteenHypothesis_of_inputs` derives mechanically.  Every field below
therefore names a real §7–§16 obligation, not a repackaging of something already
provable:

* the maximal pair `S, T`, their types, and the case-(b) trichotomy of (8.8)
  — Pf §14 / BG §16;
* the cyclic structure `W = W₁W₂`, the complements `U, V`, the primes `p, q` and
  the counting parameters `u, v, c, d` — §13–§14;
* the Dade character grids `ω, μ, ν` with the induction identities (13.1.e), the
  signs `δ, δ'`, and the integral maps `τ_S, τ_T, τ₃` — Pf §3–§9.

`sectionSixteenHypothesis_of_isMinimalSimpleOdd` reduces to exactly "produce a
`Section16Inputs G`": the design localizes the obligation to this explicit menu rather
than to an opaque `Peterfalvi.S16.Hypothesis`, and the menu is now fully supplied. -/
structure Section16Inputs (G : Type*) [Group G] [Finite G] where
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  U : Subgroup G
  V : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  S_nonI : IsTypeNonI S
  T_nonI : IsTypeNonI T
  one_typeII : IsTypeII S ∨ IsTypeII T
  theorem88_caseB :
    ∀ M : Subgroup G, M ∈ maximalSubgroups G →
      IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨
        (∃ g : G, MulAut.conj g • M = T)
  W_eq_inter : W = S ⊓ T
  W_eq_join : W = W1 ⊔ W2
  W1_inf_W2_eq_bot : W1 ⊓ W2 = ⊥
  W1_commutes_W2 : ∀ x ∈ W1, ∀ y ∈ W2, Commute x y
  W_cyclic : IsCyclic ↥W
  S_deriv_eq_PU : derivedInG S = maxNilpotentNormalHall S ⊔ U
  T_deriv_eq_QV : derivedInG T = maxNilpotentNormalHall T ⊔ V
  /-- `Q ⊓ V = ⊥`: the invariant complement `V` genuinely complements `Q = T_F` in `T'` (from
  `exists_kappaHall_invariant_complement_to_MF`, ungated by (14.9)); threaded into `S15.Hypothesis`
  as `Q_inf_V_eq_bot`. -/
  V_inf_Q_eq_bot : maxNilpotentNormalHall T ⊓ V = ⊥
  /-- `T = T' ⋊ W₂`: `W₂` complements `T'` in `T` (from `typeP_derivedInG_isComplement_kappaHall`,
  ungated by (14.9)); threaded into `S15.Hypothesis` as `W2_isComplement_T_deriv`. -/
  W2_isComplement_T_deriv :
    Subgroup.IsComplement' ((derivedInG T).subgroupOf T) (W2.subgroupOf T)
  W1_normalizes_U : W1 ≤ Subgroup.normalizer (U : Set G)
  W2_normalizes_V : W2 ≤ Subgroup.normalizer (V : Set G)
  q : ℕ
  p : ℕ
  q_prime : q.Prime
  p_prime : p.Prime
  q_eq_card_W1 : q = Nat.card ↥W1
  p_eq_card_W2 : p = Nat.card ↥W2
  u : ℕ
  v : ℕ
  c : ℕ
  d : ℕ
  c_eq_card_C : c = Nat.card ↥(U ⊓ Subgroup.centralizer (maxNilpotentNormalHall S : Set G))
  d_eq_card_D : d = Nat.card ↥(V ⊓ Subgroup.centralizer (maxNilpotentNormalHall T : Set G))
  card_U_eq_uc : Nat.card ↥U = u * c
  card_V_eq_vd : Nat.card ↥V = v * d
  Sset : Set (ClassFunction ↥S ℂ)
  Tset : Set (ClassFunction ↥T ℂ)
  A0S : Set ↥S
  A0T : Set ↥T
  tauS : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥S G
  tauT : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥T G
  omega : Fin q → Fin p → ClassFunction ↥W ℂ
  mu : Fin q → Fin p → ClassFunction ↥S ℂ
  nu : Fin q → Fin p → ClassFunction ↥T ℂ
  delta : Fin p → ℤ
  deltaPrime : Fin q → ℤ
  delta_pm_one : (∀ j : Fin p, delta j = 1 ∨ delta j = -1) ∧
    (∀ i : Fin q, deltaPrime i = 1 ∨ deltaPrime i = -1)
  mu_degree_modEq_delta : ∀ (i : Fin q) (j : Fin p), ∃ a : ℤ,
    mu i j 1 = (delta j : ℂ) + (q : ℂ) * (a : ℂ)
  delta_zero_eq_one : delta ⟨0, p_prime.pos⟩ = 1
  tau3 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥W G
  mu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_left)).toMonoidHom
          (omega i j - omega ⟨0, q_prime.pos⟩ j))
      = (delta j : ℂ) • (mu i j - mu ⟨0, q_prime.pos⟩ j)
  mu_irreducible : ∀ (i : Fin q) (j : Fin p),
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (mu i j)
  mu_col_injective : ∀ j : Fin p, Function.Injective (fun i : Fin q => mu i j)
  /-- **Peterfalvi (4.3.b), full-grid orthonormality** (issues 9076/9014): the `μ_{ij}` are
  pairwise-distinct irreducibles across the whole grid. -/
  mu_orthonormal : ∀ (i k : Fin q) (j l : Fin p),
    OddOrder.RepresentationTheory.ClassFunction.inner (mu i j) (mu k l)
      = if i = k ∧ j = l then 1 else 0
  mu_colSum_eq_induce : ∀ j : Fin p,
    ∃ ψ : ClassFunction ↥((derivedInG S).subgroupOf S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      (∑ i : Fin q, mu i j) = ClassFunction.induce ((derivedInG S).subgroupOf S) ψ ∧
      (j ≠ ⟨0, p_prime.pos⟩ →
        ¬ (((W2.subgroupOf S).subgroupOf ((derivedInG S).subgroupOf S) :
            Set ↥((derivedInG S).subgroupOf S)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ψ))
  /-- **Peterfalvi (9.8)/(9.11) reverse dichotomy (S-side R-family gate)** (issue 9092): a
  reducible member of the kernel-filter family `S(X)` over `S' = derivedInG S` is a nonzero
  `μ`-column sum.  Threaded from the `Section16CharacterData` producer. -/
  mu_reducible_dichotomy : ∀ {X : Subgroup ↥S} {ψ : ClassFunction ↥S ℂ},
    ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG S).subgroupOf S) X →
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ →
    ∃ j : Fin p, j ≠ ⟨0, p_prime.pos⟩ ∧ ψ = ∑ i : Fin q, mu i j
  nu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_right)).toMonoidHom
          (omega i j - omega i ⟨0, p_prime.pos⟩))
      = (deltaPrime i : ℂ) • (nu i j - nu i ⟨0, p_prime.pos⟩)
  /- Peterfalvi (4.3)--(4.9), T-side pure ν-grid data. -/
  nu_irreducible : ∀ (i : Fin q) (j : Fin p),
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (nu i j)
  nu_row_injective : ∀ i : Fin q, Function.Injective (fun j : Fin p => nu i j)
  nu_orthonormal : ∀ (i k : Fin q) (j l : Fin p),
    OddOrder.RepresentationTheory.ClassFunction.inner (nu i j) (nu k l)
      = if i = k ∧ j = l then 1 else 0
  nu_degree_modEq_deltaPrime : ∀ (i : Fin q) (j : Fin p), ∃ a : ℤ,
    nu i j 1 = (deltaPrime i : ℂ) + (p : ℂ) * (a : ℂ)
  deltaPrime_zero_eq_one : deltaPrime ⟨0, q_prime.pos⟩ = 1
  nu_rowSum_eq_induce : ∀ i : Fin q,
    ∃ ψ : ClassFunction ↥((derivedInG T).subgroupOf T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      (∑ j : Fin p, nu i j)
        = ClassFunction.induce ((derivedInG T).subgroupOf T) ψ ∧
      (i ≠ ⟨0, q_prime.pos⟩ →
        ¬ (((W1.subgroupOf T).subgroupOf ((derivedInG T).subgroupOf T) :
            Set ↥((derivedInG T).subgroupOf T)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ψ))
  nu_reducible_dichotomy : ∀ {X : Subgroup ↥T} {ψ : ClassFunction ↥T ℂ},
    ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG T).subgroupOf T) X →
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ →
    ∃ i : Fin q, i ≠ ⟨0, q_prime.pos⟩ ∧ ψ = ∑ j : Fin p, nu i j
  nu_diff_support : ∀ (Tdata : TypePData T), Tdata.U = V →
    Tdata.W1 = W2 → Tdata.W2 = W1 → ∀ (j : Fin p) {i k : Fin q},
    i ≠ ⟨0, q_prime.pos⟩ → k ≠ ⟨0, q_prime.pos⟩ →
    nu i j 1 = nu k j 1 →
    (nu i j - nu k j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S10.typePACore0 T Tdata) T
  nu_apply_of_not_mem_W1 : ∀ (i : Fin q) (j : Fin p) (w : G)
    (hwW : w ∈ W) (hwT : w ∈ T), w ∉ (W1 : Set G) →
    nu i j ⟨w, hwT⟩ = (deltaPrime i : ℂ) * omega i j ⟨w, hwW⟩
  nu_conj : ∀ (i : Fin q) (j : Fin p),
    (nu i j).conj =
      nu (OddOrder.Peterfalvi.S15.finNeg q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg p_prime.pos j)
  q_lt_p : q < p
  /-- **Peterfalvi (13.1.b) carrier (S-side)**: the type-`P` data of `S` with its complement `U`
  and cyclic factor `W₁` reconciled to the menu's `U`/`W1`.  Sourced from the `tp` producer
  (`Section16TypePStructure.Sdata`); threaded into `S15.Hypothesis` to discharge its U-side. -/
  Sdata : TypePData S
  Sdata_U_eq : Sdata.U = U
  Sdata_W1_eq : Sdata.W1 = W1
  /-- **Peterfalvi (13.2.a) U-side**: `U` abelian (BG Lemma 15.1(b), `U` the `(κ∪σ)'`-Hall). -/
  S_U_commutative : IsMulCommutative ↥U
  /-- **W₂-reconciliation**: intrinsic `Sdata.W2 = C_{S'}(W₁#)` equals abstract `W₂` (= `K*`). -/
  Sdata_W2_eq : Sdata.W2 = W2
  /-- **Peterfalvi (4.8), `μ`-column-difference support** (issues 9076/9014): nontrivial
  equal-degree columns have `A₀(S)`-supported `μ`-differences. -/
  mu_diff_support : ∀ (i : Fin q) {j k : Fin p},
    j ≠ ⟨0, p_prime.pos⟩ → k ≠ ⟨0, p_prime.pos⟩ →
    mu i j 1 = mu i k 1 →
    (mu i j - mu i k).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S10.typePACore0 S Sdata) S
  /-- **Peterfalvi (4.3.c), value identity** (Coq `prTIirr_id`; issues 9076/9014): on `W ∖ W₂`
  the `μ`-grid is the signed `ω`-grid, `μ_{ij}(w) = δ_j·ω_{ij}(w)`. -/
  mu_apply_of_not_mem_W2 : ∀ (i : Fin q) (j : Fin p) (w : G) (hwW : w ∈ W)
    (hwS : w ∈ S), w ∉ (W2 : Set G) →
    mu i j ⟨w, hwS⟩ = (delta j : ℂ) * omega i j ⟨w, hwW⟩
  /-- **Peterfalvi (4.9)(a)**: CF-level conjugation symmetry `μ̄_{ij} = μ_{−i,−j}`. -/
  mu_conj : ∀ (i : Fin q) (j : Fin p),
    (mu i j).conj = mu (OddOrder.Peterfalvi.S15.finNeg q_prime.pos i)
      (OddOrder.Peterfalvi.S15.finNeg p_prime.pos j)
  /-- **Peterfalvi (3.9.a)**: CF-level conjugation symmetry of the `τ₃∘ω` grid,
  `(τ₃ω_{ij})̄ = τ₃ω_{−i,−j}` — the `η`-grid conj-pair in the pre-`η` form of this layer. -/
  tau3_omega_conj : ∀ (i : Fin q) (j : Fin p),
    (tau3 (omega i j)).conj
      = tau3 (omega (OddOrder.Peterfalvi.S15.finNeg q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg p_prime.pos j))
  /- Grid property fields (issue 3002): the (3.2)/(3.3)/(3.4) character-theoretic content of
  `tau3`/`omega`, threaded from `Section16CharacterData` into `S15.Hypothesis`. -/
  /-- **Peterfalvi (3.2), isometry part**: `τ₃` preserves the class-function inner product. -/
  tau3_isometry : OddOrder.Peterfalvi.S07.IsIntegralIsometry tau3
  /-- **Peterfalvi (3.2)**: `τ₃` sends the trivial character to the trivial character. -/
  tau3_trivial : tau3 (trivialClassFunction ↥W) = trivialClassFunction G
  /-- **Peterfalvi (3.2.c)**: on the regular set `W ∖ (W₁ ∪ W₂)` the map `τ₃` is the identity. -/
  tau3_apply_of_regular : ∀ (α : ClassFunction ↥W ℂ) (w : G) (hwW : w ∈ W),
    w ∉ (W1 : Set G) ∪ (W2 : Set G) → tau3 α w = α ⟨w, hwW⟩
  /-- **Peterfalvi (3.2)**: `τ₃` sends virtual characters to virtual characters. -/
  tau3_mem_ZIrr : ∀ z ∈ ZIrr ↥W, tau3 z ∈ ZIrr G
  /-- **Peterfalvi (3.3)/(3.4)**: the `ω`-grid is orthonormal. -/
  omega_orthonormal : ∀ (i k : Fin q) (j l : Fin p),
    ClassFunction.inner (omega i j) (omega k l) = if i = k ∧ j = l then 1 else 0
  /-- The `ω_{ij}` are linear characters: `ω_{ij}(1) = 1`. -/
  omega_apply_one : ∀ (i : Fin q) (j : Fin p), omega i j 1 = 1
  /-- Each `ω_{ij}` is a virtual character (in fact an irreducible character of `W`). -/
  omega_mem_ZIrr : ∀ (i : Fin q) (j : Fin p), omega i j ∈ ZIrr ↥W
  /-- **Peterfalvi (3.3)** (issue 2033): each `ω_{ij}` is multiplicative — a linear character. -/
  omega_mul : ∀ (i : Fin q) (j : Fin p) (w w' : ↥W),
    omega i j (w * w') = omega i j w * omega i j w'
  /-- **Peterfalvi (3.3)** (issue 2033): the column-`0` characters `ω_{i0}` are trivial on `W₂`. -/
  omega_col_zero_apply_of_mem_W2 : ∀ (i : Fin q) (w : ↥W), (w : G) ∈ W2 →
    omega i ⟨0, p_prime.pos⟩ w = 1
  /-- **Peterfalvi (3.3)** (issue 2033): the row-`0` characters `ω_{0j}` are trivial on `W₁`. -/
  omega_row_zero_apply_of_mem_W1 : ∀ (j : Fin p) (w : ↥W), (w : G) ∈ W1 →
    omega ⟨0, q_prime.pos⟩ j w = 1
  /-- **Peterfalvi (3.3)** (issue 2033): on `W₁` the grid values are `q`-th roots of unity. -/
  omega_pow_q_of_mem_W1 : ∀ (i : Fin q) (j : Fin p) (w : ↥W), (w : G) ∈ W1 →
    omega i j w ^ q = 1
  /-- **Peterfalvi (3.3)** (issue 2033): on `W₂` the grid values are `p`-th roots of unity. -/
  omega_pow_p_of_mem_W2 : ∀ (i : Fin q) (j : Fin p) (w : ↥W), (w : G) ∈ W2 →
    omega i j w ^ p = 1
  /-- **Peterfalvi (3.2.d)** (issue 2034): a class function of `G` orthogonal to the whole
  `τ₃ω`-grid vanishes on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` — the grid enumerates the
  `σ`-image, and every irreducible off the image vanishes on `Ŵ`. -/
  eta_complete_vanish : ∀ χ : ClassFunction G ℂ,
    (∀ (i : Fin q) (j : Fin p), ClassFunction.inner (tau3 (omega i j)) χ = 0) →
    ∀ w : G, w ∈ W → w ∉ (W1 : Set G) ∪ (W2 : Set G) → χ w = 0
  /-- **Peterfalvi (3.4)/(3.5), the four-corner vanishing** (issue 2036): off the conjugacy
  saturation of the regular set `Ŵ = W ∖ (W₁ ∪ W₂)`, the `(3.5)` relation collapses to
  `1 − (τ₃ω)_{i0}(x) − (τ₃ω)_{0j}(x) + (τ₃ω)_{ij}(x) = 0` for nonzero row/column indices. -/
  eta_fourcorner_vanish : ∀ (i : Fin q) (j : Fin p), i ≠ ⟨0, q_prime.pos⟩ →
    j ≠ ⟨0, p_prime.pos⟩ → ∀ x : G,
    x ∉ OddOrder.GroupTheory.conjClassSet ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) →
    (1 : ℂ) - tau3 (omega i ⟨0, p_prime.pos⟩) x - tau3 (omega ⟨0, q_prime.pos⟩ j) x
      + tau3 (omega i j) x = 0
  /-- **Peterfalvi (3.9.b), row-vanishing transport** (issue 2036): if `(τ₃ω)₁₀` vanishes at
  `x`, so do all `(τ₃ω)_{i0}` with `i ≠ 0` — the nontrivial row characters are Galois-conjugate
  powers of `ω₁₀`, and the twist fixes the vanishing value. -/
  eta_row_vanish_of_one_zero : ∀ x : G,
    tau3 (omega ⟨1, q_prime.one_lt⟩ ⟨0, p_prime.pos⟩) x = 0 →
    ∀ i : Fin q, i ≠ ⟨0, q_prime.pos⟩ → tau3 (omega i ⟨0, p_prime.pos⟩) x = 0
  /-- **Peterfalvi (3.9.b), full row-axis Galois orbit**: every nonprincipal
  `(τ₃ω)_{i0}` is coefficient-Galois conjugate to `(τ₃ω)_{10}`. -/
  eta_row_galois_orbit : ∀ i : Fin q, i ≠ ⟨0, q_prime.pos⟩ →
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u (tau3 (omega ⟨1, q_prime.one_lt⟩ ⟨0, p_prime.pos⟩)) =
        tau3 (omega i ⟨0, p_prime.pos⟩)
  /-- **Peterfalvi (3.9.b), full column-axis Galois orbit**: every nonprincipal
  `(τ₃ω)_{0j}` is coefficient-Galois conjugate to `(τ₃ω)_{01}`. -/
  eta_column_galois_orbit : ∀ j : Fin p, j ≠ ⟨0, p_prime.pos⟩ →
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u (tau3 (omega ⟨0, q_prime.pos⟩ ⟨1, p_prime.one_lt⟩)) =
        tau3 (omega ⟨0, q_prime.pos⟩ j)
  /-- **Peterfalvi (3.9.c)** (issue-3002 keystone): on elements of order prime to `pq`, the
  `η`-grid values `(τ₃ω)_{ij}(g)` are rational integers. -/
  eta_intCast_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    ∀ (i : Fin q) (j : Fin p), ∃ m : ℤ, tau3 (omega i j) g = (m : ℂ)
  /-- **Peterfalvi (3.9.a)** (issue-3002 keystone): on elements of order prime to `pq`, the
  `η`-grid pairs under the index negation `(i,j) ↦ (−i,−j)` (`S15.finNeg`). -/
  eta_pair_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    ∀ (i : Fin q) (j : Fin p),
      tau3 (omega (OddOrder.Peterfalvi.S15.finNeg q_prime.pos i)
              (OddOrder.Peterfalvi.S15.finNeg p_prime.pos j)) g
        = tau3 (omega i j) g
  /-- **Peterfalvi (3.9)** (issue-3002 keystone): the principal grid value is `η₀₀(g) = 1`. -/
  eta_principal_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    tau3 (omega ⟨0, q_prime.pos⟩ ⟨0, p_prime.pos⟩) g = 1

/-- **Peterfalvi §13 coherent Dade-grid output** — *owned by lane-b*.

The character grids `ω, μ, ν` with the induction identities (13.1.e), the signs
`δ, δ'`, the integral maps `τ_S, τ_T, τ₃`, and the exceptional-character data
`Sset, Tset, A0S, A0T`.  Sibling references are taken from `mp` (for `S, T`) and
`tp` (for `W, p, q` and the structural facts).  Producer:
`section16CharacterData_of_isMinimalSimpleOdd` (Peterfalvi §3–§13 coherent grids). -/
structure Section16CharacterData {G : Type*} [Group G] [Finite G]
    (mp : Section16MaximalPair G) (tp : Section16TypePStructure mp) where
  Sset : Set (ClassFunction ↥mp.S ℂ)
  Tset : Set (ClassFunction ↥mp.T ℂ)
  A0S : Set ↥mp.S
  A0T : Set ↥mp.T
  tauS : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥mp.S G
  tauT : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥mp.T G
  omega : Fin tp.q → Fin tp.p → ClassFunction ↥tp.W ℂ
  mu : Fin tp.q → Fin tp.p → ClassFunction ↥mp.S ℂ
  nu : Fin tp.q → Fin tp.p → ClassFunction ↥mp.T ℂ
  delta : Fin tp.p → ℤ
  deltaPrime : Fin tp.q → ℤ
  delta_pm_one : (∀ j : Fin tp.p, delta j = 1 ∨ delta j = -1) ∧
    (∀ i : Fin tp.q, deltaPrime i = 1 ∨ deltaPrime i = -1)
  mu_degree_modEq_delta : ∀ (i : Fin tp.q) (j : Fin tp.p), ∃ a : ℤ,
    mu i j 1 = (delta j : ℂ) + (tp.q : ℂ) * (a : ℂ)
  delta_zero_eq_one : delta ⟨0, tp.p_prime.pos⟩ = 1
  tau3 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥tp.W G
  mu_definition : ∀ (i : Fin tp.q) (j : Fin tp.p),
    ClassFunction.induce (tp.W.subgroupOf mp.S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq tp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (omega i j - omega ⟨0, tp.q_prime.pos⟩ j))
      = (delta j : ℂ) • (mu i j - mu ⟨0, tp.q_prime.pos⟩ j)
  mu_irreducible : ∀ (i : Fin tp.q) (j : Fin tp.p),
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (mu i j)
  mu_col_injective : ∀ j : Fin tp.p, Function.Injective (fun i : Fin tp.q => mu i j)
  /-- **Peterfalvi (4.3.b), full-grid orthonormality** (issues 9076/9014): the `μ_{ij}` are
  pairwise-distinct irreducibles across the whole grid. -/
  mu_orthonormal : ∀ (i k : Fin tp.q) (j l : Fin tp.p),
    OddOrder.RepresentationTheory.ClassFunction.inner (mu i j) (mu k l)
      = if i = k ∧ j = l then 1 else 0
  /-- **Peterfalvi (4.8)** (issues 9076/9014): `A₀(S)`-support of the `μ`-column differences. -/
  mu_diff_support : ∀ (i : Fin tp.q) {j k : Fin tp.p},
    j ≠ ⟨0, tp.p_prime.pos⟩ → k ≠ ⟨0, tp.p_prime.pos⟩ →
    mu i j 1 = mu i k 1 →
    (mu i j - mu i k).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S10.typePACore0 mp.S tp.Sdata) mp.S
  /-- **Peterfalvi (4.3.c), value identity** (Coq `prTIirr_id`; issues 9076/9014): on `W ∖ W₂`
  the `μ`-grid is the signed `ω`-grid, `μ_{ij}(w) = δ_j·ω_{ij}(w)`. -/
  mu_apply_of_not_mem_W2 : ∀ (i : Fin tp.q) (j : Fin tp.p) (w : G) (hwW : w ∈ tp.W)
    (hwS : w ∈ mp.S), w ∉ (tp.W2 : Set G) →
    mu i j ⟨w, hwS⟩ = (delta j : ℂ) * omega i j ⟨w, hwW⟩
  /-- **Peterfalvi (4.9)(a)**: CF-level conjugation symmetry `μ̄_{ij} = μ_{−i,−j}`. -/
  mu_conj : ∀ (i : Fin tp.q) (j : Fin tp.p),
    (mu i j).conj = mu (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
      (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
  /-- **Peterfalvi (3.9.a)**: CF-level conjugation symmetry of the `τ₃∘ω` grid,
  `(τ₃ω_{ij})̄ = τ₃ω_{−i,−j}` — the `η`-grid conj-pair in the pre-`η` form of this layer. -/
  tau3_omega_conj : ∀ (i : Fin tp.q) (j : Fin tp.p),
    (tau3 (omega i j)).conj
      = tau3 (omega (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j))
  mu_colSum_eq_induce : ∀ j : Fin tp.p,
    ∃ ψ : ClassFunction ↥((derivedInG mp.S).subgroupOf mp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      (∑ i : Fin tp.q, mu i j) = ClassFunction.induce ((derivedInG mp.S).subgroupOf mp.S) ψ ∧
      (j ≠ ⟨0, tp.p_prime.pos⟩ →
        ¬ (((tp.W2.subgroupOf mp.S).subgroupOf ((derivedInG mp.S).subgroupOf mp.S) :
            Set ↥((derivedInG mp.S).subgroupOf mp.S)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ψ))
  /-- **Peterfalvi (9.8)/(9.11) reverse dichotomy (S-side R-family gate)** (issue 9092): a
  reducible member of the kernel-filter family `S(X)` over `S' = derivedInG mp.S` is a nonzero
  `μ`-column sum.  Supplied at the producer from the §6 certain-type identity. -/
  mu_reducible_dichotomy : ∀ {X : Subgroup ↥mp.S} {ψ : ClassFunction ↥mp.S ℂ},
    ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG mp.S).subgroupOf mp.S) X →
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ →
    ∃ j : Fin tp.p, j ≠ ⟨0, tp.p_prime.pos⟩ ∧ ψ = ∑ i : Fin tp.q, mu i j
  nu_definition : ∀ (i : Fin tp.q) (j : Fin tp.p),
    ClassFunction.induce (tp.W.subgroupOf mp.T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq tp.W_eq_inter).trans inf_le_right)).toMonoidHom
          (omega i j - omega i ⟨0, tp.p_prime.pos⟩))
      = (deltaPrime i : ℂ) • (nu i j - nu i ⟨0, tp.p_prime.pos⟩)
  /- Peterfalvi (4.3)--(4.9), T-side pure ν-grid data.  These fields mirror the
  μ-side grounding data and are kept independent of the post-(14.9) structural
  fact that V is commutative. -/
  nu_irreducible : ∀ (i : Fin tp.q) (j : Fin tp.p),
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (nu i j)
  nu_row_injective : ∀ i : Fin tp.q, Function.Injective (fun j : Fin tp.p => nu i j)
  nu_orthonormal : ∀ (i k : Fin tp.q) (j l : Fin tp.p),
    OddOrder.RepresentationTheory.ClassFunction.inner (nu i j) (nu k l)
      = if i = k ∧ j = l then 1 else 0
  nu_degree_modEq_deltaPrime : ∀ (i : Fin tp.q) (j : Fin tp.p), ∃ a : ℤ,
    nu i j 1 = (deltaPrime i : ℂ) + (tp.p : ℂ) * (a : ℂ)
  deltaPrime_zero_eq_one : deltaPrime ⟨0, tp.q_prime.pos⟩ = 1
  nu_rowSum_eq_induce : ∀ i : Fin tp.q,
    ∃ ψ : ClassFunction ↥((derivedInG mp.T).subgroupOf mp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      (∑ j : Fin tp.p, nu i j)
        = ClassFunction.induce ((derivedInG mp.T).subgroupOf mp.T) ψ ∧
      (i ≠ ⟨0, tp.q_prime.pos⟩ →
        ¬ (((tp.W1.subgroupOf mp.T).subgroupOf
            ((derivedInG mp.T).subgroupOf mp.T) :
              Set ↥((derivedInG mp.T).subgroupOf mp.T)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ψ))
  nu_reducible_dichotomy : ∀ {X : Subgroup ↥mp.T} {ψ : ClassFunction ↥mp.T ℂ},
    ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG mp.T).subgroupOf mp.T) X →
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ →
    ∃ i : Fin tp.q, i ≠ ⟨0, tp.q_prime.pos⟩ ∧ ψ = ∑ j : Fin tp.p, nu i j
  nu_diff_support : ∀ (Tdata : TypePData mp.T), Tdata.U = tp.V →
    Tdata.W1 = tp.W2 → Tdata.W2 = tp.W1 → ∀ (j : Fin tp.p) {i k : Fin tp.q},
    i ≠ ⟨0, tp.q_prime.pos⟩ → k ≠ ⟨0, tp.q_prime.pos⟩ →
    nu i j 1 = nu k j 1 →
    (nu i j - nu k j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S10.typePACore0 mp.T Tdata) mp.T
  nu_apply_of_not_mem_W1 : ∀ (i : Fin tp.q) (j : Fin tp.p) (w : G)
    (hwW : w ∈ tp.W) (hwT : w ∈ mp.T), w ∉ (tp.W1 : Set G) →
    nu i j ⟨w, hwT⟩ = (deltaPrime i : ℂ) * omega i j ⟨w, hwW⟩
  nu_conj : ∀ (i : Fin tp.q) (j : Fin tp.p),
    (nu i j).conj =
      nu (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
  /- Grid property fields (issue 3002): the (3.2)/(3.3)/(3.4) character-theoretic content of
  `tau3`/`omega`, supplied by the producer from `tau3W_isometry` etc. and `omegaS_inner` etc. -/
  /-- **Peterfalvi (3.2), isometry part**: `τ₃` preserves the class-function inner product. -/
  tau3_isometry : OddOrder.Peterfalvi.S07.IsIntegralIsometry tau3
  /-- **Peterfalvi (3.2)**: `τ₃` sends the trivial character to the trivial character. -/
  tau3_trivial : tau3 (trivialClassFunction ↥tp.W) = trivialClassFunction G
  /-- **Peterfalvi (3.2.c)**: on the regular set `W ∖ (W₁ ∪ W₂)` the map `τ₃` is the identity. -/
  tau3_apply_of_regular : ∀ (α : ClassFunction ↥tp.W ℂ) (w : G) (hwW : w ∈ tp.W),
    w ∉ (tp.W1 : Set G) ∪ (tp.W2 : Set G) → tau3 α w = α ⟨w, hwW⟩
  /-- **Peterfalvi (3.2)**: `τ₃` sends virtual characters to virtual characters. -/
  tau3_mem_ZIrr : ∀ z ∈ ZIrr ↥tp.W, tau3 z ∈ ZIrr G
  /-- **Peterfalvi (3.3)/(3.4)**: the `ω`-grid is orthonormal. -/
  omega_orthonormal : ∀ (i k : Fin tp.q) (j l : Fin tp.p),
    ClassFunction.inner (omega i j) (omega k l) = if i = k ∧ j = l then 1 else 0
  /-- The `ω_{ij}` are linear characters: `ω_{ij}(1) = 1`. -/
  omega_apply_one : ∀ (i : Fin tp.q) (j : Fin tp.p), omega i j 1 = 1
  /-- Each `ω_{ij}` is a virtual character (in fact an irreducible character of `W`). -/
  omega_mem_ZIrr : ∀ (i : Fin tp.q) (j : Fin tp.p), omega i j ∈ ZIrr ↥tp.W
  /-- **Peterfalvi (3.3)** (issue 2033): each `ω_{ij}` is multiplicative — a linear character. -/
  omega_mul : ∀ (i : Fin tp.q) (j : Fin tp.p) (w w' : ↥tp.W),
    omega i j (w * w') = omega i j w * omega i j w'
  /-- **Peterfalvi (3.3)** (issue 2033): the column-`0` characters `ω_{i0}` are trivial on `W₂`. -/
  omega_col_zero_apply_of_mem_W2 : ∀ (i : Fin tp.q) (w : ↥tp.W), (w : G) ∈ tp.W2 →
    omega i ⟨0, tp.p_prime.pos⟩ w = 1
  /-- **Peterfalvi (3.3)** (issue 2033): the row-`0` characters `ω_{0j}` are trivial on `W₁`. -/
  omega_row_zero_apply_of_mem_W1 : ∀ (j : Fin tp.p) (w : ↥tp.W), (w : G) ∈ tp.W1 →
    omega ⟨0, tp.q_prime.pos⟩ j w = 1
  /-- **Peterfalvi (3.3)** (issue 2033): on `W₁` the grid values are `q`-th roots of unity. -/
  omega_pow_q_of_mem_W1 : ∀ (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W), (w : G) ∈ tp.W1 →
    omega i j w ^ tp.q = 1
  /-- **Peterfalvi (3.3)** (issue 2033): on `W₂` the grid values are `p`-th roots of unity. -/
  omega_pow_p_of_mem_W2 : ∀ (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W), (w : G) ∈ tp.W2 →
    omega i j w ^ tp.p = 1
  /-- **Peterfalvi (3.2.d)** (issue 2034): a class function of `G` orthogonal to the whole
  `τ₃ω`-grid vanishes on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` — the grid enumerates the
  `σ`-image, and every irreducible off the image vanishes on `Ŵ`. -/
  eta_complete_vanish : ∀ χ : ClassFunction G ℂ,
    (∀ (i : Fin tp.q) (j : Fin tp.p), ClassFunction.inner (tau3 (omega i j)) χ = 0) →
    ∀ w : G, w ∈ tp.W → w ∉ (tp.W1 : Set G) ∪ (tp.W2 : Set G) → χ w = 0
  /-- **Peterfalvi (3.4)/(3.5), the four-corner vanishing** (issue 2036): off the conjugacy
  saturation of the regular set `Ŵ = W ∖ (W₁ ∪ W₂)`, the `(3.5)` relation collapses to
  `1 − (τ₃ω)_{i0}(x) − (τ₃ω)_{0j}(x) + (τ₃ω)_{ij}(x) = 0` for nonzero row/column indices. -/
  eta_fourcorner_vanish : ∀ (i : Fin tp.q) (j : Fin tp.p), i ≠ ⟨0, tp.q_prime.pos⟩ →
    j ≠ ⟨0, tp.p_prime.pos⟩ → ∀ x : G,
    x ∉ OddOrder.GroupTheory.conjClassSet ((tp.W : Set G) \ ((tp.W1 : Set G) ∪ (tp.W2 : Set G))) →
    (1 : ℂ) - tau3 (omega i ⟨0, tp.p_prime.pos⟩) x - tau3 (omega ⟨0, tp.q_prime.pos⟩ j) x
      + tau3 (omega i j) x = 0
  /-- **Peterfalvi (3.9.b), row-vanishing transport** (issue 2036): if `(τ₃ω)₁₀` vanishes at
  `x`, so do all `(τ₃ω)_{i0}` with `i ≠ 0` — the nontrivial row characters are Galois-conjugate
  powers of `ω₁₀`, and the twist fixes the vanishing value. -/
  eta_row_vanish_of_one_zero : ∀ x : G,
    tau3 (omega ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩) x = 0 →
    ∀ i : Fin tp.q, i ≠ ⟨0, tp.q_prime.pos⟩ → tau3 (omega i ⟨0, tp.p_prime.pos⟩) x = 0
  /-- **Peterfalvi (3.9.b), full row-axis Galois orbit.** -/
  eta_row_galois_orbit : ∀ i : Fin tp.q, i ≠ ⟨0, tp.q_prime.pos⟩ →
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u
          (tau3 (omega ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩)) =
        tau3 (omega i ⟨0, tp.p_prime.pos⟩)
  /-- **Peterfalvi (3.9.b), full column-axis Galois orbit.** -/
  eta_column_galois_orbit : ∀ j : Fin tp.p, j ≠ ⟨0, tp.p_prime.pos⟩ →
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u
          (tau3 (omega ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩)) =
        tau3 (omega ⟨0, tp.q_prime.pos⟩ j)
  /-- **Peterfalvi (3.9.c)** (issue-3002 keystone): on elements of order prime to `pq`, the
  `η`-grid values `(τ₃ω)_{ij}(g)` are rational integers.  Supplied from
  `tau3W_omegaS_intCast_of_coprime` (S05 σ-Galois integrality). -/
  eta_intCast_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (tp.p * tp.q) →
    ∀ (i : Fin tp.q) (j : Fin tp.p), ∃ m : ℤ, tau3 (omega i j) g = (m : ℂ)
  /-- **Peterfalvi (3.9.a)** (issue-3002 keystone): on elements of order prime to `pq`, the
  `η`-grid pairs under the index negation `(i,j) ↦ (−i,−j)` (`S15.finNeg`). -/
  eta_pair_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (tp.p * tp.q) →
    ∀ (i : Fin tp.q) (j : Fin tp.p),
      tau3 (omega (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
              (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)) g
        = tau3 (omega i j) g
  /-- **Peterfalvi (3.9)** (issue-3002 keystone): the principal grid value is `η₀₀(g) = 1`. -/
  eta_principal_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (tp.p * tp.q) →
    tau3 (omega ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩) g = 1

/-- The chosen cyclic factor: `data.W₁ = K` (definitional). -/
theorem typePData_of_kappaHall_hallComplement_W1 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : BG.Ch4.S14.IsTypeP2 M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) (hUM : U ≤ M)
    (hUhall : Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa M ∪ BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G)) :
    (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).W1 = K := by
  unfold typePData_of_kappaHall_hallComplement
    BG.Ch4.S16.typePData_of_isTypeP_of_inputs BG.Ch4.S16.typePData_of_inputs
  rfl

/-- The chosen complement: `data.U = U` (definitional). -/
theorem typePData_of_kappaHall_hallComplement_U {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : BG.Ch4.S14.IsTypeP2 M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) (hUM : U ≤ M)
    (hUhall : Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa M ∪ BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G)) :
    (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).U = U := by
  unfold typePData_of_kappaHall_hallComplement
    BG.Ch4.S16.typePData_of_isTypeP_of_inputs BG.Ch4.S16.typePData_of_inputs
  rfl

/-- The dual factor: `data.W2 = K*` (`= M_σ ⊓ C(K)`).  Via the (8.4.b) centralizer law
`C_{M'}(k) = K*` (`typeP_derivedInG_inf_centralizer_kappaElement_eq`) applied to a nonidentity
`k ∈ W₁ = K` (`data.centralizer_W1`).  This reconciles the intrinsic `TypePData.W2` with the
maximal-pair dual factor `mp.Kstar`, discharging the `Sdata.W2 = W2` obligation of §15's
`card_P_eq` / `basic_structure_gated.P_order`. -/
theorem typePData_of_kappaHall_hallComplement_W2 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K U Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : BG.Ch4.S14.IsTypeP2 M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) (hUM : U ≤ M)
    (hUhall : Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa M ∪ BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G))
    (hKstar : Kstar = BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).W2 = Kstar := by
  have := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  obtain ⟨⟨x, hxK⟩, hxne⟩ := exists_ne (1 : ↥K)
  have hxne' : x ≠ 1 := by rintro rfl; exact hxne rfl
  have hW1 :
      (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).W1 = K :=
    typePData_of_kappaHall_hallComplement_W1 hG hM hP2 hKM hKne hK hUM hUhall hKnorm
  have hxW1 : x ∈
      (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).W1 := by
    rw [hW1]; exact hxK
  have hcen :=
    (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).centralizer_W1
      x hxW1 hxne'
  have hkstar :=
    BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq hG hM hP2.1 hKM hK hKstar
      x hxK hxne'
  exact hcen.symm.trans hkstar

/-- **Type-P structure engine from the type data** (`sorry`-free, gated-endpoint skeleton).

Given the Peterfalvi type data (`TypePData`) of both members of the maximal pair, this assembles
the full `Section16TypePStructure` with the pairing factors `W₁ = S`'s cyclic complement,
`W₂ = T`'s cyclic complement, `U, V` the type-data complements, and `W = S ∩ T`.  The fields that
are *intrinsic to a single member* are discharged directly from the type data:

* `S_deriv_eq_PU`/`T_deriv_eq_QV` from `TypePData.derivedInG_eq_fitting_sup_U` (`M' = M_F ⊔ U`);
* `q_prime`/`p_prime` from the supplied primality of `|W₁(S)|`, `|W₁(T)|` (carried by
  `TypePNontrivialCore` for type II–IV);
* the counting identities `|U| = u·c`, `|V| = v·d` by Lagrange (`C = U ∩ C_G(M_F) ≤ U`).

The *genuinely cross-member* facts — that `S ∩ T` is exactly the cyclic product
`W₁(S) × W₁(T)` (BG §16 / Peterfalvi (8.9) pairing), the normalization `W₁ ≤ N_G(U)`
(Peterfalvi (13.1.b), "remark following Def (8.4)"), and the ordering `q < p` — remain explicit
hypotheses.  Discharging them for the canonical pair is the residual obligation of the producer
`section16TypePStructure_of_isMinimalSimpleOdd` (issue 7005). -/
noncomputable def section16TypePStructure_of_components {G : Type*} [Group G] [Finite G]
    {mp : Section16MaximalPair G} (W1 W2 U V : Subgroup G)
    (hSderiv : derivedInG mp.S = maxNilpotentNormalHall mp.S ⊔ U)
    (hTderiv : derivedInG mp.T = maxNilpotentNormalHall mp.T ⊔ V)
    (hVinfQ : maxNilpotentNormalHall mp.T ⊓ V = ⊥)
    (hW2compl : Subgroup.IsComplement' ((derivedInG mp.T).subgroupOf mp.T) (W2.subgroupOf mp.T))
    (hSprime : (Nat.card ↥W1).Prime) (hTprime : (Nat.card ↥W2).Prime)
    (hWjoin : mp.S ⊓ mp.T = W1 ⊔ W2)
    (hWcyc : IsCyclic ↥(mp.S ⊓ mp.T))
    (hbot : W1 ⊓ W2 = ⊥)
    (hcomm : ∀ x ∈ W1, ∀ y ∈ W2, Commute x y)
    (hSnorm : W1 ≤ Subgroup.normalizer (U : Set G))
    (hTnorm : W2 ≤ Subgroup.normalizer (V : Set G))
    (hlt : Nat.card ↥W1 < Nat.card ↥W2)
    (Sd : TypePData mp.S) (hSdU : Sd.U = U) (hSdW1 : Sd.W1 = W1) (hSdW2 : Sd.W2 = W2)
    (hUcomm : IsMulCommutative ↥U) :
    Section16TypePStructure mp where
  W1 := W1
  W2 := W2
  W := mp.S ⊓ mp.T
  U := U
  V := V
  W_eq_inter := rfl
  W_eq_join := hWjoin
  W1_inf_W2_eq_bot := hbot
  W1_commutes_W2 := hcomm
  W_cyclic := hWcyc
  S_deriv_eq_PU := hSderiv
  T_deriv_eq_QV := hTderiv
  V_inf_Q_eq_bot := hVinfQ
  W2_isComplement_T_deriv := hW2compl
  W1_normalizes_U := hSnorm
  W2_normalizes_V := hTnorm
  q := Nat.card ↥W1
  p := Nat.card ↥W2
  q_prime := hSprime
  p_prime := hTprime
  q_eq_card_W1 := rfl
  p_eq_card_W2 := rfl
  u := Nat.card ↥U /
    Nat.card ↥(U ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.S : Set G))
  v := Nat.card ↥V /
    Nat.card ↥(V ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.T : Set G))
  c := Nat.card ↥(U ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.S : Set G))
  d := Nat.card ↥(V ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.T : Set G))
  c_eq_card_C := rfl
  d_eq_card_D := rfl
  card_U_eq_uc := (Nat.div_mul_cancel (Subgroup.card_dvd_of_le inf_le_left)).symm
  card_V_eq_vd := (Nat.div_mul_cancel (Subgroup.card_dvd_of_le inf_le_left)).symm
  q_lt_p := hlt
  Sdata := Sd
  Sdata_U_eq := hSdU
  Sdata_W1_eq := hSdW1
  S_U_commutative := hUcomm
  Sdata_W2_eq := hSdW2

/-- **BG §14 type-P duality producer** — *lane-f* (BG §14 `typeP_duality`).
Given the maximal pair, constructs the cyclic structure `W = W₁W₂`, the complements
`U, V`, the primes `p, q`, and the counting parameters.

In gated-endpoint-skeleton form (issue 7005), with `mp` now carrying the canonical partner
witness: the **W-side** (the pairing `S ∩ T = K × K*` cyclic, `K ⊓ K* = 1`, commuting) is
discharged `sorry`-free from `mp`'s κ-Hall data via `typeP_pair_W_structure` (BG Theorem 14.7).
The design localized the rest to the **U-side menu** — the semidirect complements `U, V` with
`M' = M_F ⊔ U` and `K ≤ N_G(U)` (Peterfalvi (13.1.b), "remark following Def (8.4)"), the
primality of `|K|, |K*|` (BG Theorem C(10); type II–IV via the type data, Type-V via the
partner argument), and the ordering `q < p` (Peterfalvi (13.2.a)) — and that menu is now
supplied in full. -/
noncomputable def section16TypePStructure_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (mp : Section16MaximalPair G) :
    Section16TypePStructure mp := by
  -- **W-side** from `mp`'s canonical partner witness (`typeP_pair_W_structure`, BG 14.7).  A Hall
  -- `(κ ∪ σ)'`-subgroup `U₀` of `S` (needed only to invoke the lemma) comes from Hall's theorem.
  haveI : Group.IsSolvable ↥mp.S := hG.isSolvable_of_mem_maximalSubgroups mp.S_maximal
  have hUex : ∃ U₀ : Subgroup G,
      Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa mp.S ∪ BG.Ch3.S10.sigma mp.S)ᶜ)
        (U₀.subgroupOf mp.S) := by
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥mp.S)
      ((BG.Ch4.S14.kappa mp.S ∪ BG.Ch3.S10.sigma mp.S)ᶜ)
    exact ⟨U'.map mp.S.subtype, by
      rw [show (U'.map mp.S.subtype).subgroupOf mp.S = U' from
        Subgroup.comap_map_eq_self_of_injective mp.S.subtype_injective U']
      exact hU'⟩
  have hU₀' := hUex.choose_spec
  obtain ⟨hWjoin, hWcyc, hbot, hcomm⟩ :=
    BG.Ch4.S16.typeP_pair_W_structure hG mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall mp.Kstar_eq
      hU₀' mp.T_maximal mp.T_typeP mp.S_T_not_conj mp.Kstar_le_T mp.Kstar_hall mp.Z_cyclic mp.K_eq
  -- **Primes** `|K|, |K*|` from **Peterfalvi (10.11)** (`theorem88_caseB_prime_orders`): the
  -- orders of the two factors of the case-(b) cyclic group are prime.  The case-(b) data is built
  -- directly from `mp` (`W₁ = K`, `W₂ = K*`, `W = K ⊔ K*` cyclic).  This delegates the primality —
  -- a Peterfalvi §10–12 character-theoretic fact — to its named home, where it is owned (lane-b).
  -- `K`, `K*` are cyclic as subgroups of the cyclic `Z = K ⊔ K*` (needed below and for the
  -- `typeP_derivedInG_isComplement_kappaHall` instance argument in the case-(b) primality data).
  haveI : IsCyclic ↥(mp.K ⊔ mp.Kstar) := mp.Z_cyclic
  haveI : IsCyclic ↥mp.K :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_left : mp.K ≤ mp.K ⊔ mp.Kstar))
      (Subgroup.inclusion_injective _)
  haveI : IsCyclic ↥mp.Kstar :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_right : mp.Kstar ≤ mp.K ⊔ mp.Kstar))
      (Subgroup.inclusion_injective _)
  -- **BG Theorem 14.7(e)**: `Ẑ = (K ⊔ K*) − (K ∪ K*)` is a TI-set with normalizer-bound `K ⊔ K*`.
  -- This conjunct of the duality does not mention the partner, so the `∃!` witness need not be
  -- identified with `mp.T`.  It supplies Peterfalvi (8.4.e) for `W = K ⊔ K*` below.
  have hZti : IsTISubset (BG.Ch4.S14.zTilde mp.K mp.Kstar) (mp.K ⊔ mp.Kstar) := by
    obtain ⟨_, hMstP⟩ := (BG.Ch4.S14.typeP_duality hG mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
      mp.Kstar_eq).2.2.exists
    exact hMstP.2.2.2.2.2.1
  -- **S-side `TypePData` carrier** (relane #4, issue 4010): the chosen complement
  -- `U = hScompl.choose` to `M_F` in `S'` is the `(κ∪σ)'`-Hall
  -- (`S10Interface.isHall_kappaSigmaCompl_of_isTypeP2_complement`, using `mp.S_typeP2`), so
  -- `typePData_of_kappaHall_hallComplement` produces a `TypePData mp.S` with `.W₁ = mp.K = W1` and
  -- `.U = U`, reconciling the carrier to the structure's factors.
  have hScompl := BG.Ch4.S14.exists_kappaHall_invariant_complement_to_MF hG
    mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
  have hTcompl := BG.Ch4.S14.exists_kappaHall_invariant_complement_to_MF hG
    mp.T_maximal mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
  have hUM : hScompl.choose ≤ mp.S :=
    (le_sup_right.trans_eq hScompl.choose_spec.1.symm).trans (Subgroup.map_subtype_le _)
  have hUhall :=
    Peterfalvi.S10Interface.isHall_kappaSigmaCompl_of_isTypeP2_complement hG mp.S_maximal
      mp.S_typeP2 hUM
    hScompl.choose_spec.1 hScompl.choose_spec.2.2
  have hKne : mp.K ≠ ⊥ := fun h =>
    BG.Ch4.S14.card_kappaHall_ne_one mp.S_typeP mp.K_le_S mp.K_hall (Subgroup.card_eq_one.mpr h)
  have hKstarne : mp.Kstar ≠ ⊥ := fun h =>
    BG.Ch4.S14.card_kappaHall_ne_one mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
      (Subgroup.card_eq_one.mpr h)
  have hprimes := Peterfalvi.S12.theorem88_caseB_prime_orders hG hnoV
    { S := mp.S, T := mp.T, W1 := mp.K, W2 := mp.Kstar, W := mp.K ⊔ mp.Kstar,
      S_maximal := mp.S_maximal, T_maximal := mp.T_maximal, S_ne_T := mp.S_ne_T,
      W_eq := rfl, W_cyclic := mp.Z_cyclic,
      -- `W = K × K*` and both factors nontrivial (8.8.b): the disjointness is the BG 14.7
      -- pairing (`typeP_pair_W_structure`), the nontriviality the κ-Hall order bound.
      W1_inf_W2_eq_bot := hbot,
      W1_nontrivial := hKne, W2_nontrivial := hKstarne,
      -- (8.4.e) for `W = K ⊔ K*`: the BG 14.7 TI-set `Ẑ` inside the cyclic (hence abelian) host.
      normalizer_V := Peterfalvi.S10.normalizer_V_of_isTISubset mp.Z_cyclic hZti,
      S_nonI := mp.S_nonI, T_nonI := mp.T_nonI, one_typeII := mp.one_typeII,
      W1_le_S := mp.K_le_S, W2_le_T := mp.Kstar_le_T,
      -- (8.8.b1): the κ-Hall factors complement the derived subgroups —
      -- `typeP_derivedInG_isComplement_kappaHall` (BG Thm 14.7(h), proved + axiom-clean), the
      -- BG↔Peterfalvi identification of BG's `κ(M)`-Hall with Peterfalvi's `W₁(M)`.
      S_compl := BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG mp.S_maximal mp.S_typeP
        mp.K_le_S mp.K_hall,
      T_compl := BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG mp.T_maximal mp.T_typeP
        mp.Kstar_le_T mp.Kstar_hall,
      -- (8.8.b1) last clause `S ∩ T = W` and (8.8.b4) the covering.
      S_inf_T_eq_W := hWjoin, cover := mp.theorem88_caseB }
  -- **U-side residual**: the (13.1.b) semidirect complements `U, V` (with `M' = M_F ⊔ U` and
  -- `K ≤ N_G(U)`) and the ordering `q < p`.  A *true*, constructible §13/§14 statement for the
  -- canonical pair (`mp.K`, `mp.Kstar`).
  -- **U-side** from Peterfalvi (13.1.b): the κ-Hall-invariant complement `U` to `M_F` in `M'`
  -- (`exists_kappaHall_invariant_complement_to_MF` = invariant Schur–Zassenhaus, BG §1 Prop
  -- 1.5(b)).
  -- The ordering `|K| < |K*|` is carried by the relabelled pair (`mp.K_lt_Kstar`), so the residual
  -- is now fully discharged.
  -- `Section16TypePStructure mp` is `Type`-valued, so we cannot `obtain` the `∃`-witness into the
  -- goal (`Exists.casesOn` only eliminates into `Prop`).  Extract the data with `Exists.choose`.
  exact section16TypePStructure_of_components mp.K mp.Kstar hScompl.choose hTcompl.choose
    hScompl.choose_spec.1 hTcompl.choose_spec.1 hTcompl.choose_spec.2.2
    (BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG mp.T_maximal mp.T_typeP mp.Kstar_le_T
      mp.Kstar_hall)
    hprimes.1 hprimes.2
    hWjoin hWcyc hbot hcomm hScompl.choose_spec.2.1 hTcompl.choose_spec.2.1 mp.K_lt_Kstar
    (typePData_of_kappaHall_hallComplement hG mp.S_maximal mp.S_typeP2 mp.K_le_S hKne mp.K_hall
      hUM hUhall hScompl.choose_spec.2.1)
    (typePData_of_kappaHall_hallComplement_U hG mp.S_maximal mp.S_typeP2 mp.K_le_S hKne mp.K_hall
      hUM hUhall hScompl.choose_spec.2.1)
    (typePData_of_kappaHall_hallComplement_W1 hG mp.S_maximal mp.S_typeP2 mp.K_le_S hKne mp.K_hall
      hUM hUhall hScompl.choose_spec.2.1)
    (typePData_of_kappaHall_hallComplement_W2 hG mp.S_maximal mp.S_typeP2 mp.K_le_S hKne mp.K_hall
      hUM hUhall hScompl.choose_spec.2.1 mp.Kstar_eq)
    (BG.Ch4.S15.typeP_hall_derived_eq_and_abelian hG mp.S_maximal mp.K_le_S hUM hKne mp.K_hall
      hUhall).2

end

end OddOrder

-- ===== OddOrder/FeitThompsonSetup.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

/-- `K` of `certainTypeS` is `(derivedInG mp.S).subgroupOf mp.S` (the (4.2) convention `K = S'`;
same literal field as the `Sdata`-instance `typePData_toS06Hypothesis`, so the two §6 Hypothesis
instances of `S` share `K` on the nose — issue 2038 `hyp46Smp` shortcut). -/
theorem certainTypeS_K_eq :
    (mp.certainTypeS hG).K = (derivedInG mp.S).subgroupOf mp.S := by
  unfold Section16MaximalPair.certainTypeS certainTypeHypothesis_of_typeP_kappaHall; rfl

variable (tp : Section16TypePStructure mp)

/-- `K` of `certainTypeT` is `(derivedInG mp.T).subgroupOf mp.T` (the (4.2) convention
`K = T'`). -/
theorem certainTypeT_K_eq :
    (mp.certainTypeT hG).K = (derivedInG mp.T).subgroupOf mp.T := by
  unfold Section16MaximalPair.certainTypeT certainTypeHypothesis_of_typeP_kappaHall; rfl

/-- `|certainTypeT.W₁| = tp.p` (both are `|mp.Kstar|`). -/
theorem cardCertainTypeT_W1 : Nat.card ↥(mp.certainTypeT hG).W1 = tp.p := by
  rw [certainTypeT_W1_eq hG mp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe mp.Kstar_le_T).toEquiv,
    ← tp.W2_eq_Kstar hG, ← tp.p_eq_card_W2]

/-- **Column negation is character inversion** (Peterfalvi (3.5)/(3.9.a) power-grid pairing,
`W₂`-column half): `chi2enum ((p − j) % p) = (chi2enum j)⁻¹`. -/
theorem chi2enum_finNeg (j : Fin tp.p) :
    chi2enum hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = (chi2enum hG mp tp j)⁻¹ := by
  have := (mp.certainTypeS hG).sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W
  rw [chi2enum]
  refine OddOrder.Peterfalvi.S06.cyclicPowEnum_eq_inv_of_add_mod_eq_zero _ ?_
  change ((tp.p - (j : ℕ)) % tp.p + (j : ℕ)) % tp.p = 0
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
  · simp [h0]
  · have hj : (j : ℕ) < tp.p := j.2
    rw [Nat.mod_eq_of_lt (by omega : tp.p - (j : ℕ) < tp.p),
      Nat.sub_add_cancel hj.le, Nat.mod_self]

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

/-- The `eqQ` reindex fixes the base index `0`. -/
theorem eqQ_zero : eqQ hG mp tp ⟨0, tp.q_prime.pos⟩ = 0 := by
  apply Fin.ext; simp [eqQ]

/-- **The S-side (13.1.e) `mu_definition` identity** — the cd producer's `mu_definition` field for
the
S-side grid.  Inducing the transported `ω`-column difference `Ind_W^S(ω_{ij} − ω_{0j})` gives the
signed `μ`-difference `δ_j (μ_{ij} − μ_{0j})`, via `S06.induce_chiColumn_diff_mu_diff` after the
`compHom`/`subgroupCongr` transport collapse. -/
theorem muS_definition (i : Fin tp.q) (j : Fin tp.p) :
    ClassFunction.induce (tp.W.subgroupOf mp.S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (omegaS hG mp tp i j - omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j))
      = (deltaS hG mp tp j : ℂ) • (muS hG mp tp i j - muS hG mp tp ⟨0, tp.q_prime.pos⟩ j) := by
  have key : ∀ k : Fin tp.q,
      ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (omegaS hG mp tp k j)
        = ClassFunction.compHom (MulEquiv.subgroupCongr (tpW_subgroupOf_eq hG mp tp)).toMonoidHom
            ((mp.certainTypeS hG).chiColumn (chi2enum hG mp tp j) (eqQ hG mp tp k) :
              ClassFunction ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W ℂ) := by
    intro k
    rw [omegaS, ClassFunction.compHom_comp]
    congr 1
  rw [ClassFunction.compHom_sub, key i, key ⟨0, tp.q_prime.pos⟩, ← ClassFunction.compHom_sub,
    eqQ_zero hG mp tp, induce_compHom_subgroupCongr (tpW_subgroupOf_eq hG mp tp)]
  simp only [deltaS, muS, eqQ_zero hG mp tp, Int.cast_smul_eq_zsmul]
  exact (mp.certainTypeS hG).induce_chiColumn_diff_mu_diff (chi2enum hG mp tp j) (eqQ hG mp tp i)

/-- **A linear character of `↥tp.W` is determined by its restrictions to `tp.W1` and `tp.W2`.**
Since `tp.W = tp.W1 ⊔ tp.W2` is an internal product of two commuting subgroups, every `w : ↥tp.W`
factors as `w = a * b` with `a ∈ tp.W1`, `b ∈ tp.W2`; two monoid homs agreeing on `tp.W1` and
`tp.W2`
therefore agree everywhere.  This is the generating-set half of the S/T-shared-`ω` symmetry. -/
theorem monoidHom_eq_of_eqOn_W1_W2 {χ χ' : ↥tp.W →* ℂˣ}
    (h1 : ∀ w : ↥tp.W, (w : G) ∈ tp.W1 → χ w = χ' w)
    (h2 : ∀ w : ↥tp.W, (w : G) ∈ tp.W2 → χ w = χ' w) :
    χ = χ' := by
  have := tp.W_cyclic
  let : CommGroup ↥tp.W := IsCyclic.commGroup
  have hW1le : tp.W1 ≤ tp.W := by rw [tp.W_eq_join]; exact le_sup_left
  have hW2le : tp.W2 ≤ tp.W := by rw [tp.W_eq_join]; exact le_sup_right
  have htop : (tp.W1.subgroupOf tp.W) ⊔ (tp.W2.subgroupOf tp.W) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← tp.W_eq_join, Subgroup.subgroupOf_self]
  ext w
  have hmem : w ∈ (tp.W1.subgroupOf tp.W) ⊔ (tp.W2.subgroupOf tp.W) := htop ▸ Subgroup.mem_top w
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [← hab, map_mul, map_mul, h1 a (Subgroup.mem_subgroupOf.mp ha),
    h2 b (Subgroup.mem_subgroupOf.mp hb)]

/-- **The S-side (4.3.c) value identity** (Coq `prTIirr_id`, `PFsection4.v:403`) — the cd
producer's `mu_apply_of_not_mem_W2` field: on `W ∖ W₂` the `μ`-grid is the signed `ω`-grid,
`μ_{ij}(w) = δ_j·ω_{ij}(w)`.  The §6 value identity `certainType_apply_eq_of_mem_V` at
`certainTypeS` (Dade-free, base-`Hypothesis` level), with the `sdiff.V`-membership built from
`tpW_subgroupOf_eq`/`certainTypeS_W2_eq` and the `chiColumn`/`omegaS` transport collapsing
along `gridEquivE` (`gridEquivE_coe` is `rfl`). -/
theorem muS_apply_of_not_mem_W2 (i : Fin tp.q) (j : Fin tp.p) (w : G) (hwW : w ∈ tp.W)
    (hwS : w ∈ mp.S) (hw2 : w ∉ (tp.W2 : Set G)) :
    muS hG mp tp i j ⟨w, hwS⟩
      = (deltaS hG mp tp j : ℂ) * omegaS hG mp tp i j ⟨w, hwW⟩ := by
  have hjoin : (⟨w, hwS⟩ : ↥mp.S) ∈ (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
    rw [← tpW_subgroupOf_eq hG mp tp]
    exact Subgroup.mem_subgroupOf.mpr hwW
  have hnot : (⟨w, hwS⟩ : ↥mp.S) ∉ ((mp.certainTypeS hG).W2 : Set ↥mp.S) := by
    intro hmem
    apply hw2
    rw [tp.W2_eq_Kstar hG]
    have hks := (certainTypeS_W2_eq hG mp) ▸ hmem
    exact Subgroup.mem_subgroupOf.mp hks
  have hv : (⟨w, hwS⟩ : ↥mp.S) ∈ (mp.certainTypeS hG).sdiffTICyclicHypothesis.V :=
    ⟨SetLike.mem_coe.mpr hjoin, hnot⟩
  have h43c := (mp.certainTypeS hG).certainType_apply_eq_of_mem_V
    (chi2enum hG mp tp j) (eqQ hG mp tp i) hv
  refine (show muS hG mp tp i j ⟨w, hwS⟩
      = (((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).mu (eqQ hG mp tp i) :
          ClassFunction ↥mp.S ℂ) ⟨w, hwS⟩ from rfl).trans (h43c.trans ?_)
  rw [omegaS, ClassFunction.compHom_apply]
  show (((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).sign : ℂ) * _
      = (deltaS hG mp tp j : ℂ) * _
  congr 1

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- **Value of `certainTypeS`'s product character on a transported `mp.K`-element**: only the
`W₁`-factor `a` survives (`wFst` is the identity, `wSnd` is trivial, on a `W₁`-element).  This is
the
`tp.W1`-restriction value used (with its `tp.W2` mirror) to discharge the S/T-shared-`ω` symmetry on
the generators via `monoidHom_eq_of_eqOn_W1_W2`. -/
theorem omegaProdCharS_apply_mem_K
    (a : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE hG mp tp w)
      = a ⟨gridEquivE hG mp tp w, gridEquivE_mem_W1 hG mp tp w hw⟩ := by
  have mem := gridEquivE_mem_W1 hG mp tp w hw
  have hfst : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst (gridEquivE hG mp tp w)
      = ⟨gridEquivE hG mp tp w, mem⟩ :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst_W1_subtype ⟨gridEquivE hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd (gridEquivE hG mp tp w) = 1 :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd_W1_subtype ⟨gridEquivE hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, mul_one]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- **Value of `certainTypeS`'s product character on a transported `mp.Kstar`-element**: only the
`W₂`-factor `b` survives.  The `tp.W2`-restriction mirror of `omegaProdCharS_apply_mem_K`. -/
theorem omegaProdCharS_apply_mem_Kstar
    (a : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE hG mp tp w)
      = b ⟨gridEquivE hG mp tp w, gridEquivE_mem_W2 hG mp tp w hw⟩ := by
  have mem := gridEquivE_mem_W2 hG mp tp w hw
  have hfst : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst (gridEquivE hG mp tp w) = 1 :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst_W2_subtype ⟨gridEquivE hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd (gridEquivE hG mp tp w)
      = ⟨gridEquivE hG mp tp w, mem⟩ :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd_W2_subtype ⟨gridEquivE hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, one_mul]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- **Value of `certainTypeT`'s product character on a transported `mp.K`-element**: since `mp.K` is
the `W₂`-factor of `T`, only the `W₂`-factor `b` survives.  The T-side mirror of
`omegaProdCharS_apply_mem_Kstar`. -/
theorem omegaProdCharT_apply_mem_K
    (a : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE_T hG mp tp w)
      = b ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W2 hG mp tp w hw⟩ := by
  have mem := gridEquivE_T_mem_W2 hG mp tp w hw
  have hfst : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst (gridEquivE_T hG mp tp w) = 1 :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst_W2_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd (gridEquivE_T hG mp tp w)
      = ⟨gridEquivE_T hG mp tp w, mem⟩ :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd_W2_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, one_mul]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- **Value of `certainTypeT`'s product character on a transported `mp.Kstar`-element**: since
`mp.Kstar` is the `W₁`-factor of `T`, only the `W₁`-factor `a` survives.  The T-side mirror of
`omegaProdCharS_apply_mem_K`. -/
theorem omegaProdCharT_apply_mem_Kstar
    (a : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE_T hG mp tp w)
      = a ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W1 hG mp tp w hw⟩ := by
  have mem := gridEquivE_T_mem_W1 hG mp tp w hw
  have hfst : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst (gridEquivE_T hG mp tp w)
      = ⟨gridEquivE_T hG mp tp w, mem⟩ :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst_W1_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd (gridEquivE_T hG mp tp w) = 1 :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd_W1_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, mul_one]

end Section16CharacterData

end

end OddOrder

-- ===== OddOrder/FeitThompsonNuGrid.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
  (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- The round-trip through `tp.W`. -/
theorem eTS_gridEquivE_T (w : ↥tp.W) :
    eTS hG mp tp (gridEquivE_T hG mp tp w) = gridEquivE hG mp tp w := by
  simp only [eTS, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- `colT i` agrees with the S-side dual on a transported `mp.K`-element. -/
theorem colT_apply_mem_K (i : Fin tp.q) (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    colT hG mp tp i ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W2 hG mp tp w hw⟩
      = (mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)
          ⟨gridEquivE hG mp tp w, gridEquivE_mem_W1 hG mp tp w hw⟩ := by
  rw [colT, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
      ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) 1
      (eTS hG mp tp (gridEquivE_T hG mp tp w)) = _
  rw [eTS_gridEquivE_T]
  exact omegaProdCharS_apply_mem_K hG mp tp _ 1 w hw

/-- The base T-side column dual is trivial. -/
theorem colT_zero : colT hG mp tp ⟨0, tp.q_prime.pos⟩ = 1 := by
  ext x
  simp [colT, eqQ_zero, Peterfalvi.S05.TICyclicHypothesis.omegaProdChar]
  rfl

/-- Column-index negation is inversion of the transported T-side column dual. -/
theorem colT_finNeg (i : Fin tp.q) :
    colT hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
      = (colT hG mp tp i)⁻¹ := by
  have heq :
      eqQ hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        = ⟨(Nat.card ↥(mp.certainTypeS hG).W1 - ((eqQ hG mp tp i : Fin _) : ℕ))
              % Nat.card ↥(mp.certainTypeS hG).W1,
            Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩ := by
    apply Fin.ext
    simp only [eqQ, finCongr_apply, Fin.val_cast, OddOrder.Peterfalvi.S15.finNeg]
    rw [cardCertainTypeS_W1 hG mp tp]
  rw [colT, colT, heq,
    (mp.certainTypeS hG).w1CharEquiv_finNeg (eqQ hG mp tp i)]
  ext w
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.one_comp,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, Subgroup.coe_subtype,
    Function.comp_apply, MonoidHom.mul_apply,
    MonoidHom.one_apply, mul_one, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact Units.val_inv_eq_inv_val _

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- `rowDualT j` agrees with the S-side dual on a transported `mp.Kstar`-element. -/
theorem rowDualT_apply_mem_Kstar (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ mp.Kstar) :
    rowDualT hG mp tp j
        ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W1 hG mp tp w hw⟩
      = chi2enum hG mp tp j
          ⟨gridEquivE hG mp tp w, gridEquivE_mem_W2 hG mp tp w hw⟩ := by
  rw [rowDualT, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
      1 (chi2enum hG mp tp j) (eTS hG mp tp (gridEquivE_T hG mp tp w)) = _
  rw [eTS_gridEquivE_T]
  exact omegaProdCharS_apply_mem_Kstar hG mp tp 1 _ w hw

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- The base row dual is trivial. -/
theorem rowDualT_zero : rowDualT hG mp tp ⟨0, tp.p_prime.pos⟩ = 1 := by
  rw [rowDualT, chi2enum_zero,
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_one,
    MonoidHom.one_comp, MonoidHom.one_comp]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- Row-index negation is inversion of the transported T-side row dual. -/
theorem rowDualT_finNeg (j : Fin tp.p) :
    rowDualT hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = (rowDualT hG mp tp j)⁻¹ := by
  rw [rowDualT, rowDualT, chi2enum_finNeg hG mp tp j]
  ext w
  simp [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar]

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- The distinguished T-side row index is zero. -/
theorem rowT_zero : rowT hG mp tp ⟨0, tp.p_prime.pos⟩ = 0 := by
  rw [rowT, rowDualT_zero]
  exact (mp.certainTypeT hG).w1CharEquiv.symm_apply_eq.mpr
    ((mp.certainTypeT hG).w1CharEquiv_zero).symm

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- The transported row enumeration intertwines `finNeg` with the certain-type `rowInv`. -/
theorem rowT_finNeg_eq_rowInv (j : Fin tp.p) :
    rowT hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = OddOrder.Peterfalvi.S06.rowInv (mp.certainTypeT hG) (rowT hG mp tp j) := by
  apply (mp.certainTypeT hG).w1CharEquiv.injective
  rw [OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv, rowT,
    Equiv.apply_symm_apply, rowDualT_finNeg hG mp tp j]
  congr 1
  rw [rowT, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The S- and T-side constructions give the same shared `ω`-grid. -/
theorem omegaS_eq_omegaT (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j = omegaT hG mp tp i j := by
  have hrow : (mp.certainTypeT hG).w1CharEquiv (rowT hG mp tp j) =
      rowDualT hG mp tp j := by
    rw [rowT, Equiv.apply_symm_apply]
  have key : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar
          (rowDualT hG mp tp j) (colT hG mp tp i)).comp
          (gridEquivE_T hG mp tp).toMonoidHom
      = ((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
          ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i))
          (chi2enum hG mp tp j)).comp (gridEquivE hG mp tp).toMonoidHom := by
    apply monoidHom_eq_of_eqOn_W1_W2
    · intro w hw
      rw [tp.W1_eq_K hG] at hw
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [omegaProdCharT_apply_mem_K hG mp tp _ _ w hw,
        colT_apply_mem_K hG mp tp i w hw]
      exact (omegaProdCharS_apply_mem_K hG mp tp _ _ w hw).symm
    · intro w hw
      rw [tp.W2_eq_Kstar hG] at hw
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [omegaProdCharT_apply_mem_Kstar hG mp tp _ _ w hw,
        rowDualT_apply_mem_Kstar hG mp tp j w hw]
      exact (omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hw).symm
  simp only [omegaS, omegaT, Peterfalvi.S06.Hypothesis.chiColumn,
    Peterfalvi.S05.TICyclicHypothesis.omega]
  rw [hrow, ClassFunction.compHom_linearIrreducibleCharacter,
    ClassFunction.compHom_linearIrreducibleCharacter, key]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.3)/(3.4)**: the shared `ω`-grid is orthonormal. -/
theorem omegaS_inner (i k : Fin tp.q) (j l : Fin tp.p) :
    ClassFunction.inner (omegaS hG mp tp i j) (omegaS hG mp tp k l)
      = if i = k ∧ j = l then 1 else 0 := by
  rw [omegaS, omegaS, ClassFunction.inner_compHom_mulEquiv (gridEquivE hG mp tp)]
  simp only [Peterfalvi.S06.Hypothesis.chiColumn]
  rw [(mp.certainTypeS hG).sdiffTICyclicHypothesis.omega_inner]
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
  · have hne : (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
        ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) (chi2enum hG mp tp j)
        ≠ (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
          ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp k)) (chi2enum hG mp tp l) := by
      intro hc
      obtain ⟨h1, h2⟩ :=
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_inj hc
      exact h ⟨(eqQ hG mp tp).injective
          ((mp.certainTypeS hG).w1CharEquiv_injective h1),
        (chi2enum hG mp tp).injective h2⟩
    rw [if_neg hne, if_neg h]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- Distinct index pairs give distinct members of the shared `ω`-grid. -/
theorem omegaS_pair_injective :
    Function.Injective
      (fun ij : Fin tp.q × Fin tp.p => omegaS hG mp tp ij.1 ij.2) := by
  intro ⟨i, j⟩ ⟨k, l⟩ hω
  change omegaS hG mp tp i j = omegaS hG mp tp k l at hω
  by_contra hne
  have h1 := omegaS_inner hG mp tp i k j l
  rw [hω] at h1
  have h2 := omegaS_inner hG mp tp k k l l
  rw [h1] at h2
  have hcond : ¬ (i = k ∧ j = l) := fun ⟨h1', h2'⟩ => hne (by rw [h1', h2'])
  rw [if_neg hcond, if_pos (⟨rfl, rfl⟩ : k = k ∧ l = l)] at h2
  exact zero_ne_one h2

/-- The transported T-side row enumeration is injective. -/
theorem rowT_injective : Function.Injective (rowT hG mp tp) := by
  intro j l hrow
  have hω : omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j =
      omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ l := by
    rw [omegaS_eq_omegaT hG mp tp, omegaS_eq_omegaT hG mp tp]
    simp only [omegaT, hrow]
  have hp : ((⟨0, tp.q_prime.pos⟩ : Fin tp.q), j) =
      ((⟨0, tp.q_prime.pos⟩ : Fin tp.q), l) :=
    omegaS_pair_injective hG mp tp hω
  exact congrArg Prod.snd hp

/-- The transported T-side column enumeration is injective. -/
theorem colT_injective : Function.Injective (colT hG mp tp) := by
  intro i k hcol
  have hω : omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩ =
      omegaS hG mp tp k ⟨0, tp.p_prime.pos⟩ := by
    rw [omegaS_eq_omegaT hG mp tp, omegaS_eq_omegaT hG mp tp]
    simp only [omegaT, hcol]
  have hp : (i, (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) =
      (k, (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) :=
    omegaS_pair_injective hG mp tp hω
  exact congrArg Prod.fst hp

/-- The transported T-side row enumeration is bijective. -/
theorem rowT_bijective : Function.Bijective (rowT hG mp tp) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨rowT_injective hG mp tp, ?_⟩
  simp only [Fintype.card_fin]
  exact (cardCertainTypeT_W1 hG mp tp).symm

/-- Reindexing equivalence for the T-side rows. -/
noncomputable def rowTEquiv :
    Fin tp.p ≃ Fin (Nat.card ↥(mp.certainTypeT hG).W1) :=
  Equiv.ofBijective (rowT hG mp tp) (rowT_bijective hG mp tp)

/-- Every entry of the canonical T-side `ν`-grid is irreducible. -/
theorem nuT_irreducible (i : Fin tp.q) (j : Fin tp.p) :
    IsIrreducibleCharacter (nuT hG mp tp i j) :=
  (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu
    (rowT hG mp tp j)).isIrreducible

/-- Within each T-side row, the canonical `ν`-characters are pairwise distinct. -/
theorem nuT_row_injective (i : Fin tp.q) :
    Function.Injective (fun j : Fin tp.p => nuT hG mp tp i j) := by
  intro j l hν
  apply rowT_injective hG mp tp
  apply ((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).injective
  exact IrreducibleCharacter.ext hν

/-- **Peterfalvi (4.3.b), T-side**: the canonical `ν`-grid is orthonormal. -/
theorem nuT_orthonormal (i k : Fin tp.q) (j l : Fin tp.p) :
    ClassFunction.inner (nuT hG mp tp i j) (nuT hG mp tp k l)
      = if i = k ∧ j = l then 1 else 0 := by
  simp only [nuT]
  rw [irreducibleCharacter_inner_eq_ite]
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
    · rw [if_neg (fun hc => hjl (rowT_injective hG mp tp
          ((((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).injective) hc))),
        if_neg (by simp [hjl])]
  · rw [if_neg ((mp.certainTypeT hG).columnFamily_mu_ne
        (fun hc => hik (colT_injective hG mp tp hc)) _ _),
      if_neg (by simp [hik])]

/-- **Peterfalvi (4.3.c), T-side** (Coq `prTIirr_id`, `PFsection4.v:403`): on
`W ∖ W₁` the canonical `ν`-grid is the signed shared `ω`-grid,
`ν_{ij}(w) = δ'_i·ω_{ij}(w)`. -/
theorem nuT_apply_of_not_mem_W1 (i : Fin tp.q) (j : Fin tp.p) (w : G)
    (hwW : w ∈ tp.W) (hwT : w ∈ mp.T) (hw1 : w ∉ (tp.W1 : Set G)) :
    nuT hG mp tp i j ⟨w, hwT⟩
      = (deltaPrimeT hG mp tp i : ℂ) * omegaS hG mp tp i j ⟨w, hwW⟩ := by
  have hjoin : (⟨w, hwT⟩ : ↥mp.T) ∈
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
    rw [← tpW_subgroupOf_T_eq hG mp tp]
    exact Subgroup.mem_subgroupOf.mpr hwW
  have hnot : (⟨w, hwT⟩ : ↥mp.T) ∉ ((mp.certainTypeT hG).W2 : Set ↥mp.T) := by
    intro hmem
    apply hw1
    rw [tp.W1_eq_K hG]
    have hk := (certainTypeT_W2_eq hG mp) ▸ hmem
    exact Subgroup.mem_subgroupOf.mp hk
  have hv : (⟨w, hwT⟩ : ↥mp.T) ∈
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.V :=
    ⟨SetLike.mem_coe.mpr hjoin, hnot⟩
  have h43c := (mp.certainTypeT hG).certainType_apply_eq_of_mem_V
    (colT hG mp tp i) (rowT hG mp tp j) hv
  refine (show nuT hG mp tp i j ⟨w, hwT⟩ =
      (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu
        (rowT hG mp tp j) : ClassFunction ↥mp.T ℂ) ⟨w, hwT⟩ from rfl).trans
    (h43c.trans ?_)
  rw [omegaS_eq_omegaT hG mp tp i j, omegaT, ClassFunction.compHom_apply]
  show (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).sign : ℂ) * _
      = (deltaPrimeT hG mp tp i : ℂ) * _
  congr 1

/-- **Peterfalvi (4.3.d), T-side**: `ν_{ij}(1) ≡ δ'_i (mod p)`. -/
theorem nuT_degree_modEq_deltaPrime (i : Fin tp.q) (j : Fin tp.p) : ∃ a : ℤ,
    nuT hG mp tp i j 1 = (deltaPrimeT hG mp tp i : ℂ) + (tp.p : ℂ) * (a : ℂ) := by
  obtain ⟨a, ha⟩ := (mp.certainTypeT hG).certainType_degree_modEq
    (colT hG mp tp i) (rowT hG mp tp j)
  refine ⟨a, ?_⟩
  have hp : (tp.p : ℂ) = (Nat.card ↥(mp.certainTypeT hG).W1 : ℂ) := by
    rw [cardCertainTypeT_W1 hG mp tp]
  simp only [nuT, deltaPrimeT, hp]
  exact ha

/-- **Peterfalvi (4.4), T-side**: the base sign is `δ'_0 = 1`. -/
theorem deltaPrimeT_zero_eq_one :
    deltaPrimeT hG mp tp ⟨0, tp.q_prime.pos⟩ = 1 := by
  rw [deltaPrimeT, colT_zero hG mp tp]
  exact ((mp.certainTypeT hG).certainType_zero_column_anchor).1

/-- **Peterfalvi (4.5.a), T-side**: each canonical `ν`-row sum is induced from an
irreducible character of `T'`, and a non-anchor row is nontrivial on `tp.W1`. -/
theorem nuT_rowSum_eq_induce (i : Fin tp.q) :
    ∃ ψ : ClassFunction ↥((derivedInG mp.T).subgroupOf mp.T) ℂ,
      IsIrreducibleCharacter ψ ∧
      (∑ j : Fin tp.p, nuT hG mp tp i j) =
        ClassFunction.induce ((derivedInG mp.T).subgroupOf mp.T) ψ ∧
      (i ≠ ⟨0, tp.q_prime.pos⟩ →
        ¬ (((tp.W1.subgroupOf mp.T).subgroupOf
            ((derivedInG mp.T).subgroupOf mp.T) :
              Set ↥((derivedInG mp.T).subgroupOf mp.T)) ⊆
          Peterfalvi.S03.characterKernel ψ)) := by
  refine ⟨ClassFunction.restrict ((derivedInG mp.T).subgroupOf mp.T)
      (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu 0 :
        ClassFunction ↥mp.T ℂ), ?_, ?_, ?_⟩
  · exact (mp.certainTypeT hG).certainTypeRestrict_isIrreducible _
  · calc
      (∑ j : Fin tp.p, nuT hG mp tp i j) =
          ∑ j' : Fin (Nat.card ↥(mp.certainTypeT hG).W1),
            (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu j' :
              ClassFunction ↥mp.T ℂ) := by
        simp only [nuT]
        exact Equiv.sum_comp (rowTEquiv hG mp tp)
          (fun j' => (((mp.certainTypeT hG).columnFamily
            (colT hG mp tp i)).mu j' : ClassFunction ↥mp.T ℂ))
      _ = _ := ((mp.certainTypeT hG).induce_restrict_certainType_eq _).symm
  · intro hine hsub
    have hχ₂ne : colT hG mp tp i ≠ 1 := by
      rw [← colT_zero hG mp tp]
      exact fun h => hine (colT_injective hG mp tp h)
    refine (mp.certainTypeT hG).not_subset_characterKernel_chiRestrict_of_ne_one
      hχ₂ne ?_
    have hseq : ((tp.W1.subgroupOf mp.T).subgroupOf
          ((derivedInG mp.T).subgroupOf mp.T)) =
        (((mp.certainTypeT hG).W2).subgroupOf
          ((derivedInG mp.T).subgroupOf mp.T)) := by
      rw [certainTypeT_W2_eq hG mp, tp.W1_eq_K hG]
    exact hseq ▸ hsub

/-- The Dade-free Hypothesis (4.6) core on `mp.T`, reconciled with an arbitrary T-side
`TypePData`.  Its certain-type parent is exactly the canonical `nuT` producer. -/
noncomputable def hyp46TmpCore (Tdata : TypePData mp.T)
    (hW1 : Tdata.W1 = tp.W2) (hW2 : Tdata.W2 = tp.W1) :
    OddOrder.Peterfalvi.S06.Hypothesis46Core
      (OddOrder.Peterfalvi.S10.typePACore mp.T) mp.T :=
  { toHypothesis := mp.certainTypeT hG
    L_normalizes_A := fun l _ ha =>
      OddOrder.Peterfalvi.S10.typePACore_conj_mem l.2 ha
    tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis Tdata hG.odd
    tic_W1 := by
      change Tdata.W1 = _
      rw [certainTypeT_W1_eq, Subgroup.map_subgroupOf_eq_of_le mp.Kstar_le_T,
        hW1, tp.W2_eq_Kstar hG]
    tic_W2 := by
      change Tdata.W2 = _
      rw [certainTypeT_W2_eq, Subgroup.map_subgroupOf_eq_of_le (k_le_T hG mp),
        hW2, tp.W1_eq_K hG]
    tic_V := rfl
    subH := (OddOrder.BG.Ch3.S10.Msigma mp.T).subgroupOf mp.T
    subH_normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    W2_le_subH := by
      rw [certainTypeT_W2_eq, ← tp.W1_eq_K hG, ← hW2]
      refine Subgroup.subgroupOf_mono mp.T ?_
      have hW2H : Tdata.W2 ≤ Tdata.H := le_trans Tdata.W2_le inf_le_left
      rw [Tdata.H_eq] at hW2H
      exact le_trans hW2H
        (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG mp.T_maximal)
    subH_le_K := by
      rw [certainTypeT_K_eq]
      exact Subgroup.subgroupOf_mono mp.T
        (OddOrder.BG.Ch3.S10.Msigma_le_derived hG mp.T_maximal)
    A_covers := by
      intro hh hhσ hh1 x hx hx1
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxD⟩ := hx
      rw [certainTypeT_K_eq, Subgroup.mem_subgroupOf] at hxD
      rw [Subgroup.mem_subgroupOf] at hhσ
      rw [Subgroup.mem_centralizer_iff] at hxC
      rw [OddOrder.Peterfalvi.S10.mem_typePACore]
      refine ⟨hxD, ?_, (hh : G), ⟨hhσ, ?_⟩, ?_⟩
      · simpa using hx1
      · simpa using hh1
      · rw [Subgroup.mem_centralizer_iff]
        rintro g rfl
        have hcomm := hxC (hh : ↥mp.T) rfl
        have := congrArg (mp.T.subtype) hcomm
        simpa using this }

/-- **Peterfalvi (4.8), conclusion (1), T-side** (Coq `prDade_sub_TIirr_on`): for
non-anchor equal-degree rows, `ν_{ij} - ν_{kj}` is supported in
`A₀(T) = A(T) ∪ (V_T)^T`. -/
theorem nuT_diff_support (Tdata : TypePData mp.T) (_hU : Tdata.U = tp.V)
    (hW1 : Tdata.W1 = tp.W2) (hW2 : Tdata.W2 = tp.W1)
    (j : Fin tp.p) {i k : Fin tp.q}
    (hi0 : i ≠ ⟨0, tp.q_prime.pos⟩) (hk0 : k ≠ ⟨0, tp.q_prime.pos⟩)
    (hdeg : nuT hG mp tp i j 1 = nuT hG mp tp k j 1) :
    (nuT hG mp tp i j - nuT hG mp tp k j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S10.typePACore0 mp.T Tdata) mp.T := by
  classical
  have : NeZero (Nat.card ↥(hyp46TmpCore hG mp tp Tdata hW1 hW2).W1) :=
    inferInstanceAs (NeZero (Nat.card ↥(mp.certainTypeT hG).W1))
  have hχi : colT hG mp tp i ≠ 1 := by
    intro hc
    exact hi0 (colT_injective hG mp tp (hc.trans (colT_zero hG mp tp).symm))
  have hχk : colT hG mp tp k ≠ 1 := by
    intro hc
    exact hk0 (colT_injective hG mp tp (hc.trans (colT_zero hG mp tp).symm))
  intro z hz
  rw [OddOrder.RepresentationTheory.ClassFunction.mem_support] at hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact OddOrder.Peterfalvi.S06.certainType_diff_supp_subset_A0
    (hyp46TmpCore hG mp tp Tdata hW1 hW2) hχi hχk (rowT hG mp tp j) hdeg hz

/-- **Peterfalvi (4.9.a), T-side**: complex conjugation pairs the canonical grid by
`ν̄_{ij} = ν_{-i,-j}`. -/
theorem nuT_conj (i : Fin tp.q) (j : Fin tp.p) :
    (nuT hG mp tp i j).conj
      = nuT hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j) := by
  have hg2 := congrArg
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥mp.T =>
      (χ : ClassFunction ↥mp.T ℂ))
    (OddOrder.Peterfalvi.S06.certainType_mu_conj_eq (mp.certainTypeT hG)
      (colT hG mp tp i) (rowT hG mp tp j))
  simp only [IrreducibleCharacter.galoisMap_apply_coe] at hg2
  rw [nuT, nuT, colT_finNeg hG mp tp i, rowT_finNeg_eq_rowInv hG mp tp j,
    ClassFunction.conj_eq_mapRingEquiv_conjAe]
  exact hg2

/-- **Peterfalvi (13.1.e), T-side**:
`Ind_W^T (ω_{ij} - ω_{i0}) = δ'_i (ν_{ij} - ν_{i0})`. -/
theorem nuT_definition (i : Fin tp.q) (j : Fin tp.p) :
    ClassFunction.induce (tp.W.subgroupOf mp.T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq tp.W_eq_inter).trans inf_le_right)).toMonoidHom
          (omegaS hG mp tp i j - omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩))
      = (deltaPrimeT hG mp tp i : ℂ) •
          (nuT hG mp tp i j - nuT hG mp tp i ⟨0, tp.p_prime.pos⟩) := by
  have key : ∀ l : Fin tp.p,
      ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq tp.W_eq_inter).trans inf_le_right)).toMonoidHom
          (omegaS hG mp tp i l)
        = ClassFunction.compHom
            (MulEquiv.subgroupCongr (tpW_subgroupOf_T_eq hG mp tp)).toMonoidHom
            ((mp.certainTypeT hG).chiColumn (colT hG mp tp i) (rowT hG mp tp l) :
              ClassFunction ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W ℂ) := by
    intro l
    rw [omegaS_eq_omegaT hG mp tp i l, omegaT, ClassFunction.compHom_comp]
    congr 1
  rw [ClassFunction.compHom_sub, key j, key ⟨0, tp.p_prime.pos⟩,
    ← ClassFunction.compHom_sub,
    rowT_zero hG mp tp,
    induce_compHom_subgroupCongr (tpW_subgroupOf_T_eq hG mp tp)]
  simp only [deltaPrimeT, nuT, rowT_zero hG mp tp, Int.cast_smul_eq_zsmul]
  exact (mp.certainTypeT hG).induce_chiColumn_diff_mu_diff
    (colT hG mp tp i) (rowT hG mp tp j)

end Section16CharacterData

end

end OddOrder

-- ===== OddOrder/FeitThompsonPairProducer.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

/-- **BG §16 maximal-pair producer** — *lane-g* (BG §16 main results).
Constructs the maximal pair `S, T`, their type classification, and the case-(b)
trichotomy of (8.8) from a minimal simple group of odd order.

This is the first real consumer of the §16 main results.  Peterfalvi (8.8)
(`maximalSubgroup_type_dichotomy`, repackaging BG Theorem I) gives the dichotomy
"every maximal subgroup is Type I, or the type-P pair `S, T` covers everything".
The second branch supplies every field directly.  The first branch is impossible:
Peterfalvi (12.17) (`theorem88_caseB_holds`, the all-Type-I non-existence argument
of §7.11/§12) produces a *non-Type-I* maximal subgroup, which contradicts "every
maximal subgroup is Type I" via the type-exclusivity corollary of Proposition 16.1
(`not_isTypeI_of_isTypeNonI`). -/
noncomputable def section16MaximalPair_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : Section16MaximalPair G := by
  classical
  -- `exists_section16MaximalPair_data` supplies the canonical pair `S, T = Mstar` with the full
  -- κ-Hall witness data.  The four subgroup witnesses are extracted by choice (the `Exists` cannot
  -- be `rcases`'d into the `Type`-valued structure goal); the structural conjunction is an `And`
  -- (large-eliminating), so it `obtain`s into named hypotheses directly.
  have e := exists_section16MaximalPair_data hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG)
  obtain ⟨hSmax, hTmax, hSneT, hSnonI, hTnonI, hone, hcaseB, hKleS, hKhall, hKstareq,
    hStypeP, hTtypeP, hSTnconj, hKstarleT, hKstarhall, hKeq, hZcyc, hKlt⟩ :=
    e.choose_spec.choose_spec.choose_spec.choose_spec
  exact
    { S := e.choose
      T := e.choose_spec.choose
      K := e.choose_spec.choose_spec.choose
      Kstar := e.choose_spec.choose_spec.choose_spec.choose
      S_maximal := hSmax
      T_maximal := hTmax
      S_ne_T := hSneT
      S_nonI := hSnonI
      T_nonI := hTnonI
      one_typeII := hone
      theorem88_caseB := hcaseB
      K_le_S := hKleS
      K_hall := hKhall
      Kstar_eq := hKstareq
      S_typeP := hStypeP
      T_typeP := hTtypeP
      S_T_not_conj := hSTnconj
      Kstar_le_T := hKstarleT
      Kstar_hall := hKstarhall
      K_eq := hKeq
      Z_cyclic := hZcyc
      K_lt_Kstar := hKlt
      S_typeP2 := isTypeP2_of_typeP_kappaHall_lt hG hSmax hStypeP hKleS hKhall hKstareq hKlt }

end OddOrder

-- ===== OddOrder/FeitThompsonCharacterData.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.2), isometry part**: `tau3W` preserves the class-function inner product. -/
theorem tau3W_isometry :
    OddOrder.Peterfalvi.S07.IsIntegralIsometry (tau3W hG mp tp) :=
  (tiCyclicW hG mp tp).sigmaIntegral_isIntegralIsometry rfl (tiCyclicWDadeApp hG mp tp)

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.2)**: `tau3W` sends the trivial character to the trivial character. -/
theorem tau3W_trivial :
    tau3W hG mp tp (trivialClassFunction ↥tp.W) = trivialClassFunction G :=
  (tiCyclicW hG mp tp).sigmaIntegral_trivial rfl (tiCyclicWDadeApp hG mp tp)

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.2)**: `tau3W` sends virtual characters to virtual characters. -/
theorem tau3W_mem_ZIrr {z : ClassFunction ↥tp.W ℂ} (hz : z ∈ ZIrr ↥tp.W) :
    tau3W hG mp tp z ∈ ZIrr G :=
  (tiCyclicW hG mp tp).sigmaIntegral_mem_ZIrr rfl (tiCyclicWDadeApp hG mp tp) hz

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.2.c)**: on the regular set `W ∖ (W₁ ∪ W₂)` the map `tau3W` is the
identity. -/
theorem tau3W_apply_of_regular (α : ClassFunction ↥tp.W ℂ) (w : G) (hwW : w ∈ tp.W)
    (hnot : w ∉ (tp.W1 : Set G) ∪ (tp.W2 : Set G)) :
    tau3W hG mp tp α w = α ⟨w, hwW⟩ :=
  (tiCyclicW hG mp tp).sigmaIntegral_apply_of_mem_V rfl (tiCyclicWDadeApp hG mp tp) α
    (show w ∈ (tiCyclicW hG mp tp).V from ⟨hwW, hnot⟩)

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (4.3.b), full-grid orthonormality of the S-side `μ`-grid** (issues 9076/9014):
`⟨μ_{ij}, μ_{kl}⟩ = [(i,j) = (k,l)]`.  Within a column by the (1.4) family injectivity; across
columns by the certain-type cross-column distinctness `columnFamily_mu_ne`. -/
theorem muS_orthonormal (i k : Fin tp.q) (j l : Fin tp.p) :
    ClassFunction.inner (muS hG mp tp i j) (muS hG mp tp k l)
      = if i = k ∧ j = l then 1 else 0 := by
  simp only [muS]
  rw [irreducibleCharacter_inner_eq_ite]
  by_cases hjl : j = l
  · subst hjl
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
    · rw [if_neg (fun hc => hik ((eqQ hG mp tp).injective
          ((((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).injective) hc))),
        if_neg (by simp [hik])]
  · rw [if_neg ((mp.certainTypeS hG).columnFamily_mu_ne
        (fun hc => hjl ((chi2enum hG mp tp).injective hc)) _ _),
      if_neg (by simp [hjl])]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **The Dade-free (4.6) core on the `muS` producer instance** (issue 9081): the structural
fields of `hyp46Smp` — the κ-Hall grid instance, `tic` reconciliations, `M_σ(S)` kernel family,
`A(S)`-covering, and the `L`-conjugation invariance of `A(S)`
(`typePACore_conj_mem`, honest) — **without** the Dade data.  The (4.7)/(4.8)-(1) support
engines (`certainType_diff_supp_subset_A0`) run on this core, so their producer applications
(`muS_diff_support`) do not require the full `A₀(S)`-Dade package bundled by `hyp46Smp`.
Both packages are axiom-clean; the split records the support theorem's true prerequisite
boundary. -/
noncomputable def hyp46SmpCore :
    OddOrder.Peterfalvi.S06.Hypothesis46Core
      (OddOrder.Peterfalvi.S10.typePACore mp.S) mp.S :=
  { toHypothesis := mp.certainTypeS hG
    L_normalizes_A := fun l _ ha => OddOrder.Peterfalvi.S10.typePACore_conj_mem l.2 ha
    tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis tp.Sdata hG.odd
    -- The structural proofs are verbatim copies of the `hyp46Smp` fields so this core remains
    -- definitionally independent of the full `A₀(S)`-Dade package.
    tic_W1 := by
      change tp.Sdata.W1 = _
      rw [certainTypeS_W1_eq, Subgroup.map_subgroupOf_eq_of_le mp.K_le_S,
        tp.Sdata_W1_eq, tp.W1_eq_K hG]
    tic_W2 := by
      change tp.Sdata.W2 = _
      rw [certainTypeS_W2_eq, Subgroup.map_subgroupOf_eq_of_le (kstar_le_S hG mp),
        tp.Sdata_W2_eq, tp.W2_eq_Kstar hG]
    tic_V := rfl
    subH := (OddOrder.BG.Ch3.S10.Msigma mp.S).subgroupOf mp.S
    subH_normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    W2_le_subH := by
      rw [certainTypeS_W2_eq, ← tp.W2_eq_Kstar hG, ← tp.Sdata_W2_eq]
      refine Subgroup.subgroupOf_mono mp.S ?_
      have hW2H : tp.Sdata.W2 ≤ tp.Sdata.H := le_trans tp.Sdata.W2_le inf_le_left
      rw [tp.Sdata.H_eq] at hW2H
      exact le_trans hW2H
        (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG mp.S_maximal)
    subH_le_K := by
      rw [certainTypeS_K_eq]
      exact Subgroup.subgroupOf_mono mp.S
        (OddOrder.BG.Ch3.S10.Msigma_le_derived hG mp.S_maximal)
    A_covers := by
      intro hh hhσ hh1 x hx hx1
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxD⟩ := hx
      rw [certainTypeS_K_eq, Subgroup.mem_subgroupOf] at hxD
      rw [Subgroup.mem_subgroupOf] at hhσ
      rw [Subgroup.mem_centralizer_iff] at hxC
      rw [OddOrder.Peterfalvi.S10.mem_typePACore]
      refine ⟨hxD, ?_, (hh : G), ⟨hhσ, ?_⟩, ?_⟩
      · simpa using hx1
      · simpa using hh1
      · rw [Subgroup.mem_centralizer_iff]
        rintro g rfl
        have hcomm := hxC (hh : ↥mp.S) rfl
        have := congrArg (mp.S.subtype) hcomm
        simpa using this }

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (4.8) conclusion (1) on the `muS` grid** (Coq `prDade_sub_TIirr_on`; the
`(13.18)` support engine in producer vocabulary): for nontrivial equal-degree columns
`j, k ≠ 0`, the `μ`-column difference `μ_{ij} − μ_{ik}` is supported in
`A₀(S) = A(S) ∪ V^S`.  The §6 support engine `certainType_diff_supp_subset_A0` applied at the
Dade-free `hyp46SmpCore` (issue 9081), whose `toHypothesis` is the `muS` instance
`mp.certainTypeS` — no grid identification needed, and no `A₀(S)`-Dade pin in the closure. -/
theorem muS_diff_support (i : Fin tp.q) {j k : Fin tp.p}
    (hj0 : j ≠ ⟨0, tp.p_prime.pos⟩) (hk0 : k ≠ ⟨0, tp.p_prime.pos⟩)
    (hdeg : muS hG mp tp i j 1 = muS hG mp tp i k 1) :
    (muS hG mp tp i j - muS hG mp tp i k).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S10.typePACore0 mp.S tp.Sdata) mp.S := by
  classical
  have : NeZero (Nat.card ↥(hyp46SmpCore hG mp tp).W1) :=
    inferInstanceAs (NeZero (Nat.card ↥(mp.certainTypeS hG).W1))
  have hχj : chi2enum hG mp tp j ≠ 1 := by
    intro hc
    exact hj0 ((chi2enum hG mp tp).injective (hc.trans (chi2enum_zero hG mp tp).symm))
  have hχk : chi2enum hG mp tp k ≠ 1 := by
    intro hc
    exact hk0 ((chi2enum hG mp tp).injective (hc.trans (chi2enum_zero hG mp tp).symm))
  intro z hz
  rw [OddOrder.RepresentationTheory.ClassFunction.mem_support] at hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact OddOrder.Peterfalvi.S06.certainType_diff_supp_subset_A0 (hyp46SmpCore hG mp tp)
    hχj hχk (eqQ hG mp tp i) hdeg hz

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The `omegaS` are linear characters: `ω_{ij}(1) = 1`. -/
theorem omegaS_apply_one (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j 1 = 1 := by
  rw [omegaS, ClassFunction.compHom_apply, map_one]
  exact (mp.certainTypeS hG).chiColumn_apply_one _ _

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- Each `omegaS i j` is a virtual character of `↥tp.W` (the pullback along `gridEquivE` of an
irreducible character). -/
theorem omegaS_mem_ZIrr (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j ∈ ZIrr ↥tp.W := by
  rw [omegaS]
  exact ClassFunction.compHom_mem_ZIrr _
    ((mp.certainTypeS hG).chiColumn (chi2enum hG mp tp j) (eqQ hG mp tp i)).mem_ZIrr

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), linearity** (issue 2033): each `ω_{ij}` is multiplicative — a linear
character of `W`.  Discharges the `omega_mul` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_mul (i : Fin tp.q) (j : Fin tp.p) (w w' : ↥tp.W) :
    omegaS hG mp tp i j (w * w') = omegaS hG mp tp i j w * omegaS hG mp tp i j w' := by
  simp only [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    map_mul, Units.val_mul]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (3.3), column-`0` normalization** (issue 2033): the column-`0` grid characters
`ω_{i0}` are trivial on `W₂` (`chi2enum 0 = 1` is the trivial `W₂`-dual).  Discharges the
`omega_col_zero_apply_of_mem_W2` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_col_zero_apply_of_mem_W2 (i : Fin tp.q) (w : ↥tp.W) (hw : (w : G) ∈ tp.W2) :
    omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩ w = 1 := by
  have hwK : (w : G) ∈ mp.Kstar := tp.W2_eq_Kstar hG ▸ hw
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK, chi2enum_zero]
  exact Units.val_one

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (3.3), row-`0` normalization** (issue 2033): the row-`0` grid characters
`ω_{0j}` are trivial on `W₁` (`w1CharEquiv 0 = 1` is the trivial `W₁`-dual).  Discharges the
`omega_row_zero_apply_of_mem_W1` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_row_zero_apply_of_mem_W1 (j : Fin tp.p) (w : ↥tp.W) (hw : (w : G) ∈ tp.W1) :
    omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j w = 1 := by
  have hwK : (w : G) ∈ mp.K := tp.W1_eq_K hG ▸ hw
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK, eqQ_zero hG mp tp,
    (mp.certainTypeS hG).w1CharEquiv_zero]
  exact Units.val_one

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (3.3), `W₁`-value order** (issue 2033): on `W₁` the grid values are `q`-th
roots of unity — the `W₂`-factor is trivial there and the `W₁`-factor character has order
dividing `|W₁| = q`.  Discharges the `omega_pow_q_of_mem_W1` field of
`Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_pow_q_of_mem_W1 (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W1) :
    omegaS hG mp tp i j w ^ tp.q = 1 := by
  have hwK : (w : G) ∈ mp.K := tp.W1_eq_K hG ▸ hw
  have mem := gridEquivE_mem_W1 hG mp tp w hwK
  have hcard : Nat.card ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) = tp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W1_le_W).toEquiv]
    exact cardCertainTypeS_W1 hG mp tp
  have hx : (⟨gridEquivE hG mp tp w, mem⟩ :
      ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W)) ^ tp.q = 1 := by
    rw [← hcard]; exact pow_card_eq_one'
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK, ← Units.val_pow_eq_pow_val, ← map_pow,
    hx, map_one, Units.val_one]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (3.3), `W₂`-value order** (issue 2033): on `W₂` the grid values are `p`-th
roots of unity — the `W₁`-factor is trivial there and the `W₂`-factor character has order
dividing `|W₂| = p`.  Discharges the `omega_pow_p_of_mem_W2` field of
`Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_pow_p_of_mem_W2 (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W2) :
    omegaS hG mp tp i j w ^ tp.p = 1 := by
  have hwK : (w : G) ∈ mp.Kstar := tp.W2_eq_Kstar hG ▸ hw
  have mem := gridEquivE_mem_W2 hG mp tp w hwK
  have hcard : Nat.card ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) = tp.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W).toEquiv]
    exact cardCertainTypeS_W2 hG mp tp
  have hx : (⟨gridEquivE hG mp tp w, mem⟩ :
      ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W)) ^ tp.p = 1 := by
    rw [← hcard]; exact pow_card_eq_one'
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK, ← Units.val_pow_eq_pow_val, ← map_pow,
    hx, map_one, Units.val_one]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- `omegaS i j` is the `tiCyclicW`-grid character of its underlying hom. -/
theorem omegaS_eq_omega_omegaSChar (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j
      = ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)).toClassFunction := by
  ext w
  simp only [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaSChar]
  rfl

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- The row-axis underlying character is the corresponding power of the first
nonprincipal row character. -/
theorem omegaSChar_row_eq_pow (i : Fin tp.q) :
    omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩ =
      omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩ ^ (i : ℕ) := by
  let χ := (mp.certainTypeS hG).w1CharEquiv
    (eqQ hG mp tp ⟨1, tp.q_prime.one_lt⟩)
  have hpow : (mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i) = χ ^ (i : ℕ) := by
    simp [χ, OddOrder.Peterfalvi.S06.Hypothesis.w1CharEquiv,
      OddOrder.Peterfalvi.S06.cyclicPowEnum_apply, eqQ]
  unfold omegaSChar
  rw [chi2enum_zero, hpow, (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_right,
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_right]
  apply MonoidHom.ext
  intro w
  simp only [MonoidHom.comp_apply]
  exact (MonoidHom.pow_apply χ (i : ℕ) _).trans
    (MonoidHom.pow_apply
      ((χ.comp (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst).comp
        (gridEquivE hG mp tp).toMonoidHom)
      (i : ℕ) w).symm

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The column-axis underlying character is the corresponding power of the first
nonprincipal column character. -/
theorem omegaSChar_column_eq_pow (j : Fin tp.p) :
    omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j =
      omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩ ^ (j : ℕ) := by
  let χ := chi2enum hG mp tp ⟨1, tp.p_prime.one_lt⟩
  have hpow : chi2enum hG mp tp j = χ ^ (j : ℕ) := by
    simp [χ, chi2enum, OddOrder.Peterfalvi.S06.cyclicPowEnum_apply]
  have hzero : eqQ hG mp tp ⟨0, tp.q_prime.pos⟩ = 0 := by
    apply Fin.ext
    simp [eqQ]
  have hχ₀ : (mp.certainTypeS hG).w1CharEquiv
      (eqQ hG mp tp ⟨0, tp.q_prime.pos⟩) =
        (1 : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
          (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ) := by
    rw [hzero]
    exact (mp.certainTypeS hG).w1CharEquiv_zero
  unfold omegaSChar
  rw [hpow, hχ₀,
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_left,
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_left]
  apply MonoidHom.ext
  intro w
  simp only [MonoidHom.comp_apply]
  exact (MonoidHom.pow_apply χ (j : ℕ) _).trans
    (MonoidHom.pow_apply
      ((χ.comp (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd).comp
        (gridEquivE hG mp tp).toMonoidHom) (j : ℕ) w).symm

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- The concrete Dade-grid member is the S05 sigma image of its underlying
linear character. -/
theorem tau3W_omegaS_eq_sigma_omegaSChar (i : Fin tp.q) (j : Fin tp.p) :
    tau3W hG mp tp (omegaS hG mp tp i j) =
      (tiCyclicW hG mp tp).sigma rfl (tiCyclicWDadeApp hG mp tp)
        ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j) :
          ClassFunction ↥(tiCyclicW hG mp tp).W ℂ) := by
  rw [omegaS_eq_omega_omegaSChar]
  change (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ = _
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]

omit [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)] [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The cyclic factor `W = W₁ ⊔ W₂` has order `|W| = q·p` (`W₁ ∩ W₂ = ⊥`, `W₁` normalizes `W₂`
since they commute). -/
theorem cardTPW : Nat.card ↥tp.W = tp.q * tp.p := by
  have hconj : ∀ x ∈ tp.W1, ∀ a ∈ tp.W2, x * a * x⁻¹ ∈ tp.W2 := by
    intro x hx a ha
    have hc : Commute x a := tp.W1_commutes_W2 x hx a ha
    have hxa : x * a * x⁻¹ = a := by rw [hc.eq]; group
    rw [hxa]; exact ha
  have hW1norm : tp.W1 ≤ Subgroup.normalizer (tp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconj x hx a ha, fun ha => ?_⟩
    have hb := hconj x⁻¹ (tp.W1.inv_mem hx) (x * a * x⁻¹) ha
    simpa [mul_assoc] using hb
  rw [tp.W_eq_join,
    OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hW1norm
      tp.W1_inf_W2_eq_bot,
    ← tp.q_eq_card_W1, ← tp.p_eq_card_W2]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The underlying-character grid is injective: orthonormal grid characters cannot have
the same underlying linear character. -/
theorem omegaSChar_injective :
    Function.Injective
      (fun ij : Fin tp.q × Fin tp.p => omegaSChar hG mp tp ij.1 ij.2) := by
  intro ⟨i, j⟩ ⟨k, l⟩ h
  by_contra hne
  have hCF : omegaS hG mp tp i j = omegaS hG mp tp k l := by
    rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar]
    exact congrArg _ (congrArg _ h)
  have h1 := omegaS_inner hG mp tp i k j l
  rw [hCF] at h1
  have h2 := omegaS_inner hG mp tp k k l l
  rw [h1] at h2
  have hcond : ¬ (i = k ∧ j = l) := fun ⟨h1', h2'⟩ => hne (by rw [h1', h2'])
  rw [if_neg hcond, if_pos (⟨rfl, rfl⟩ : k = k ∧ l = l)] at h2
  exact zero_ne_one h2

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Exhaustion by counting**: every linear character of `↥tp.W` underlies some `omegaS i j` —
the `(i,j) ↦ omegaSChar i j` map is injective (the `omegaS` are orthonormal, hence distinct)
between types of the same cardinality `pq`. -/
theorem exists_omegaS_eq_omega (ξ : ↥tp.W →* ℂˣ) :
    ∃ (i : Fin tp.q) (j : Fin tp.p),
      omegaS hG mp tp i j = ((tiCyclicW hG mp tp).omega ξ).toClassFunction := by
  classical
  have : Fintype (↥tp.W →* ℂˣ) := Fintype.ofFinite _
  have hinj := omegaSChar_injective hG mp tp
  -- cardinalities agree: `|Fin q × Fin p| = pq = |W| = |Ŵ|`
  have hcardW : Nat.card ↥tp.W = tp.q * tp.p := cardTPW mp tp
  have hcardHom : Fintype.card (↥tp.W →* ℂˣ) = tp.q * tp.p := by
    have := tp.W_cyclic
    let : CommGroup ↥tp.W := IsCyclic.commGroup
    have : NeZero ((Monoid.exponent ↥tp.W : ℂ)) := ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
    rw [← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥tp.W ℂ]
    exact hcardW
  have hsurj : Function.Surjective
      (fun ij : Fin tp.q × Fin tp.p => omegaSChar hG mp tp ij.1 ij.2) := by
    have hbij := (Fintype.bijective_iff_injective_and_card
      (fun ij : Fin tp.q × Fin tp.p => omegaSChar hG mp tp ij.1 ij.2)).mpr
      ⟨hinj, by simp [hcardHom]⟩
    exact hbij.surjective
  obtain ⟨⟨i, j⟩, hij⟩ := hsurj ξ
  refine ⟨i, j, ?_⟩
  rw [omegaS_eq_omega_omegaSChar]
  exact congrArg _ (congrArg _ hij)

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (3.9.c) for the S-side `η`-grid** (issue-3002 supply): the grid value
`η_{ij}(g) = (τ₃ω)_{ij}(g)` is a rational integer on elements `g` of order prime to `pq`.

The value is `σ(ω(ξ_{ij}))(g)` for the underlying linear character `ξ_{ij} = omegaSChar i j`
(`omegaS_eq_omega_omegaSChar` + `sigmaIntegral_apply`).  Since `ξ_{ij}` is a character of the
cyclic `W` (`|W| = pq`, `cardTPW`), its order divides `pq`, so `Coprime(orderOf g, pq)` gives
`Coprime(orderOf g, orderOf ξ_{ij})`, and the S05 (3.9.c) Galois-integrality
`exists_intCast_sigma_omega_apply` applies. -/
theorem tau3W_omegaS_intCast_of_coprime (i : Fin tp.q) (j : Fin tp.p) {g : G}
    (hg : Nat.Coprime (orderOf g) (tp.p * tp.q)) :
    ∃ n : ℤ, tau3W hG mp tp (omegaS hG mp tp i j) g = (n : ℂ) := by
  classical
  have : Fintype ↥tp.W := Fintype.ofFinite _
  -- `orderOf (omegaSChar i j) ∣ pq`: the hom `ξ` satisfies `ξ ^ |W| = 1` and `|W| = pq`.
  have hdvd : orderOf (omegaSChar hG mp tp i j) ∣ tp.p * tp.q := by
    set ξ := omegaSChar hG mp tp i j with hξ
    have hpow : ξ ^ Fintype.card ↥tp.W = 1 := by
      ext w
      rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, pow_card_eq_one, map_one]
    have hcardW : Fintype.card ↥tp.W = tp.p * tp.q := by
      rw [← Nat.card_eq_fintype_card, cardTPW mp tp, Nat.mul_comm]
    rw [← hcardW]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hcop : (orderOf g).Coprime (orderOf (omegaSChar hG mp tp i j)) :=
    hg.coprime_dvd_right hdvd
  obtain ⟨n, hn⟩ := (tiCyclicW hG mp tp).exists_intCast_sigma_omega_apply rfl
    (tiCyclicWDadeApp hG mp tp) (omegaSChar hG mp tp i j) hcop
  refine ⟨n, ?_⟩
  rw [omegaS_eq_omega_omegaSChar]
  change (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ g = _
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  exact hn

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- The principal grid character `omegaS ⟨0⟩ ⟨0⟩` is the trivial character of `↥tp.W`:
its underlying hom is `omegaProdChar (w1CharEquiv 0) (chi2enum 0) = omegaProdChar 1 1 = 1`
(`w1CharEquiv_zero`, `chi2enum_zero`), and `omega 1 = trivialClassFunction`. -/
theorem omegaS_principal_eq_trivial :
    omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩
      = trivialClassFunction ↥tp.W := by
  have hchar : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩ = 1 := by
    have h0 : eqQ hG mp tp ⟨0, tp.q_prime.pos⟩ = 0 := by
      apply Fin.ext; simp [eqQ]
    rw [omegaSChar, h0, (mp.certainTypeS hG).w1CharEquiv_zero, chi2enum_zero]
    apply MonoidHom.ext
    intro w
    change ((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar 1 1
      ((gridEquivE hG mp tp).toMonoidHom w) : ℂˣ) = 1
    rw [(mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_one, MonoidHom.one_apply]
  rw [omegaS_eq_omega_omegaSChar, hchar]
  apply ClassFunction.ext
  intro w
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply]
  change ((1 : ↥tp.W →* ℂˣ) w : ℂ) = _
  rw [MonoidHom.one_apply, Units.val_one, trivialClassFunction_apply]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.9) principal value on generic elements** (issue-3002 supply): the principal
grid value `(τ₃ω)_{00}(g) = 1` for every `g` (the coprimality hypothesis is unused:
`omegaS₀₀` is the trivial character and `τ₃(1_W) = 1_G`). -/
theorem tau3W_omegaS_principal_of_coprime {g : G}
    (_hg : Nat.Coprime (orderOf g) (tp.p * tp.q)) :
    tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩) g = 1 := by
  rw [omegaS_principal_eq_trivial, tau3W_trivial, trivialClassFunction_apply]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **The `eqQ` reindex commutes with index negation**: `eqQ` is a `finCongr` (value-preserving
cast along `|W₁| = q`), so the `S15.finNeg` negation on `Fin tp.q` transports to the explicit
`(w₁ − ·) % w₁` negation on `Fin |W₁|` — the index form of `w1CharEquiv_finNeg`. -/
theorem eqQ_finNeg (i : Fin tp.q) :
    eqQ hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
      = ⟨(Nat.card ↥(mp.certainTypeS hG).W1 - ((eqQ hG mp tp i : Fin _) : ℕ))
            % Nat.card ↥(mp.certainTypeS hG).W1,
          Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩ := by
  apply Fin.ext
  simp only [eqQ, finCongr_apply, Fin.val_cast, OddOrder.Peterfalvi.S15.finNeg]
  rw [cardCertainTypeS_W1 hG mp tp]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Index negation is character inversion for the S-side grid characters** (Peterfalvi (3.5):
the grid is indexed by character powers, so `ω_{−i,−j} = ω_{ij}⁻¹`).  Assembled from the two
power-enumeration halves (`w1CharEquiv_finNeg` via the `eqQ` cast, `chi2enum_finNeg`) and the
coordinatewise inversion `omegaProdChar_inv`. -/
theorem omegaSChar_finNeg (i : Fin tp.q) (j : Fin tp.p) :
    omegaSChar hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = (omegaSChar hG mp tp i j)⁻¹ := by
  rw [omegaSChar, omegaSChar, eqQ_finNeg hG mp tp i,
    (mp.certainTypeS hG).w1CharEquiv_finNeg (eqQ hG mp tp i),
    chi2enum_finNeg hG mp tp j]
  -- `(ω(χ₁⁻¹, χ₂⁻¹)).comp e = (ω(χ₁, χ₂).comp e)⁻¹`: pointwise, `ℂˣ` values invert
  -- coordinatewise (`omegaProdChar` is the product of the two coordinate pullbacks).
  ext w
  simp only [MonoidHom.comp_apply, MonoidHom.inv_apply,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
  -- the row factor's `⁻¹` sits at the (defeq) `W₁ ⊔ W₂`-form hom type, where the `simp`
  -- lemmas do not fire syntactically; close it by definitional unfolding of the pointwise inv.
  congr 1
  exact Units.val_inv_eq_inv_val _

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The `eqQ` reindex intertwines row negation (`S15.finNeg`) with the character-inversion
row permutation `rowInv`: both send `i` to the index of the inverse `W₁`-character. -/
theorem eqQ_finNeg_eq_rowInv (i : Fin tp.q) :
    eqQ hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
      = OddOrder.Peterfalvi.S06.rowInv (mp.certainTypeS hG) (eqQ hG mp tp i) := by
  apply (mp.certainTypeS hG).w1CharEquiv.injective
  rw [eqQ_finNeg hG mp tp i, (mp.certainTypeS hG).w1CharEquiv_finNeg,
    OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **CF-level conjugation pairs the `μ`-grid at the negated index** (Peterfalvi (4.9)(a)):
`μ̄_{ij} = μ_{−i,−j}` — the §6 conjugation bridge `certainType_mu_conj_eq` with the two
power-enumeration index bridges (`chi2enum_finNeg`, `eqQ_finNeg_eq_rowInv`). -/
theorem muS_conj (i : Fin tp.q) (j : Fin tp.p) :
    (muS hG mp tp i j).conj
      = muS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j) := by
  have hg2 := congrArg
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥mp.S =>
      (χ : ClassFunction ↥mp.S ℂ))
    (OddOrder.Peterfalvi.S06.certainType_mu_conj_eq (mp.certainTypeS hG)
      (chi2enum hG mp tp j) (eqQ hG mp tp i))
  simp only [IrreducibleCharacter.galoisMap_apply_coe] at hg2
  rw [muS, muS, chi2enum_finNeg hG mp tp j, eqQ_finNeg_eq_rowInv hG mp tp i,
    ClassFunction.conj_eq_mapRingEquiv_conjAe]
  exact hg2

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **CF-level conjugation pairs the `η = τ₃∘ω` grid at the negated index** (Peterfalvi (3.9.a),
full CF form — strengthening the generic-element `tau3W_omegaS_pair_of_coprime` below):
`(τ₃ω_{ij})̄ = τ₃ω_{−i,−j}`.  `σ` intertwines the coefficientwise Galois action
(`sigma_mapRingEquiv_comm`), and conjugation inverts the grid character
(`galoisMap_conj_omega` + `omegaSChar_finNeg`). -/
theorem tau3W_omegaS_conj (i : Fin tp.q) (j : Fin tp.p) :
    (tau3W hG mp tp (omegaS hG mp tp i j)).conj
      = tau3W hG mp tp (omegaS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)) := by
  have hcomm := OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_mapRingEquiv_comm
    (tiCyclicW hG mp tp) rfl (tiCyclicWDadeApp hG mp tp) Complex.conjAe.toRingEquiv
    ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j))
  have hg2 := congrArg
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(tiCyclicW hG mp tp).W =>
      (χ : ClassFunction ↥(tiCyclicW hG mp tp).W ℂ))
    (OddOrder.Peterfalvi.S06.galoisMap_conj_omega (tiCyclicW hG mp tp)
      (omegaSChar hG mp tp i j))
  rw [hg2] at hcomm
  rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar, omegaSChar_finNeg,
    ClassFunction.conj_eq_mapRingEquiv_conjAe]
  exact hcomm

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (3.2.d), `η`-grid form** (issue-2034 supply): a class function of `G`
orthogonal to the whole grid `tau3W (omegaS i j)` vanishes on the regular set
`Ŵ = W ∖ (W₁ ∪ W₂)`.  Transfer of the S05 completeness
`eq_zero_of_mem_V_of_inner_chiFam_eq_zero` along the exhaustion `exists_omegaS_eq_omega`
and the `σ`-grid identification `sigma_omega`. -/
theorem tau3W_omegaS_complete_vanish (χ : ClassFunction G ℂ)
    (horth : ∀ (i : Fin tp.q) (j : Fin tp.p),
      ClassFunction.inner (tau3W hG mp tp (omegaS hG mp tp i j)) χ = 0)
    {w : G} (hwW : w ∈ tp.W) (hnot : w ∉ (tp.W1 : Set G) ∪ (tp.W2 : Set G)) :
    χ w = 0 := by
  classical
  refine OddOrder.Peterfalvi.S05.TICyclicHypothesis.eq_zero_of_mem_V_of_inner_chiFam_eq_zero
    (tiCyclicW hG mp tp) rfl (tiCyclicWDadeApp hG mp tp) (χ := χ) ?_ (show w ∈ _ from ⟨hwW, hnot⟩)
  intro a b
  obtain ⟨i, j, hij⟩ := exists_omegaS_eq_omega hG mp tp
    ((tiCyclicW hG mp tp).omegaProdChar a b)
  have hchi : (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (a, b)
      = tau3W hG mp tp (omegaS hG mp tp i j) := by
    have h1 := (tiCyclicW hG mp tp).sigma_omega rfl (tiCyclicWDadeApp hG mp tp)
      ((tiCyclicW hG mp tp).omegaProdChar a b)
    rw [(tiCyclicW hG mp tp).omegaProdEquiv_symm_omegaProdChar a b] at h1
    rw [← h1, ← hij]
    change _ = (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  rw [OddOrder.RepresentationTheory.inner_conj_symm _ χ, hchi, horth i j, star_zero]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- Values of `omegaSChar` are the `omegaS`-values. -/
theorem omegaSChar_val (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W) :
    ((omegaSChar hG mp tp i j w : ℂˣ) : ℂ) = omegaS hG mp tp i j w := by
  rw [omegaS_eq_omega_omegaSChar]
  rfl

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The first nonprincipal row-axis character has the full prime order `q`. -/
theorem orderOf_omegaSChar_row_base :
    orderOf
      (omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩) = tp.q := by
  let ξ := omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩
  have hpow : ξ ^ tp.q = 1 := by
    dsimp [ξ]
    refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_ <;>
      intro w hw <;> refine Units.ext ?_
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one]
      exact omegaS_pow_q_of_mem_W1 hG mp tp _ _ w hw
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one,
        omegaS_col_zero_apply_of_mem_W2 hG mp tp _ w hw, one_pow]
  have hzero :
      omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩ = 1 := by
    rw [omegaSChar_row_eq_pow]
    exact @pow_zero (↥tp.W →* ℂˣ) _ _
  have hne : ξ ≠ 1 := by
    intro hξ
    have hξprime : omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩
        ⟨0, tp.p_prime.pos⟩ = 1 := by simpa only [ξ] using hξ
    have hp : ((⟨1, tp.q_prime.one_lt⟩ : Fin tp.q),
        (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) =
        ((⟨0, tp.q_prime.pos⟩ : Fin tp.q),
          (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) :=
      (omegaSChar_injective hG mp tp) (hξprime.trans hzero.symm)
    have hv := congrArg (fun ij : Fin tp.q × Fin tp.p => (ij.1 : ℕ)) hp
    norm_num at hv
  have hdvd : orderOf ξ ∣ tp.q := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime tp.q_prime).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The first nonprincipal column-axis character has the full prime order `p`. -/
theorem orderOf_omegaSChar_column_base :
    orderOf
      (omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩) = tp.p := by
  let ξ := omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩
  have hpow : ξ ^ tp.p = 1 := by
    dsimp [ξ]
    refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_ <;>
      intro w hw <;> refine Units.ext ?_
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one,
        omegaS_row_zero_apply_of_mem_W1 hG mp tp _ w hw, one_pow]
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one]
      exact omegaS_pow_p_of_mem_W2 hG mp tp _ _ w hw
  have hzero :
      omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩ = 1 := by
    rw [omegaSChar_column_eq_pow]
    exact @pow_zero (↥tp.W →* ℂˣ) _ _
  have hne : ξ ≠ 1 := by
    intro hξ
    have hξprime : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩
        ⟨1, tp.p_prime.one_lt⟩ = 1 := by simpa only [ξ] using hξ
    have hp : ((⟨0, tp.q_prime.pos⟩ : Fin tp.q),
        (⟨1, tp.p_prime.one_lt⟩ : Fin tp.p)) =
        ((⟨0, tp.q_prime.pos⟩ : Fin tp.q),
          (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) :=
      (omegaSChar_injective hG mp tp) (hξprime.trans hzero.symm)
    have hv := congrArg (fun ij : Fin tp.q × Fin tp.p => (ij.2 : ℕ)) hp
    norm_num at hv
  have hdvd : orderOf ξ ∣ tp.p := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime tp.p_prime).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- Full Galois orbit of the nonprincipal row-axis `η`-characters. -/
theorem tau3W_omegaS_row_galois_orbit (i : Fin tp.q)
    (hi : i ≠ ⟨0, tp.q_prime.pos⟩) :
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u
          (tau3W hG mp tp
            (omegaS hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩)) =
        tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) := by
  let ξ := omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩
  have hi0 : (i : ℕ) ≠ 0 := by
    intro h
    apply hi
    apply Fin.ext
    simpa using h
  have hicop : (i : ℕ).Coprime (orderOf ξ) := by
    rw [show orderOf ξ = tp.q by
      simpa [ξ] using orderOf_omegaSChar_row_base hG mp tp]
    exact Nat.coprime_comm.mp (tp.q_prime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi0) i.isLt))
  obtain ⟨u, hu, -⟩ :=
    (tiCyclicW hG mp tp).exists_mapRingEquiv_sigma_omega_pow rfl
      (tiCyclicWDadeApp hG mp tp) ξ hicop
  refine ⟨u, ?_⟩
  rw [tau3W_omegaS_eq_sigma_omegaSChar, tau3W_omegaS_eq_sigma_omegaSChar]
  rw [omegaSChar_row_eq_pow hG mp tp i]
  convert hu.symm using 1
  all_goals simp [ξ]
  all_goals rfl

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- Full Galois orbit of the nonprincipal column-axis `η`-characters. -/
theorem tau3W_omegaS_column_galois_orbit (j : Fin tp.p)
    (hj : j ≠ ⟨0, tp.p_prime.pos⟩) :
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u
          (tau3W hG mp tp
            (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩)) =
        tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j) := by
  let ξ := omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩
  have hj0 : (j : ℕ) ≠ 0 := by
    intro h
    apply hj
    apply Fin.ext
    simpa using h
  have hjcop : (j : ℕ).Coprime (orderOf ξ) := by
    rw [show orderOf ξ = tp.p by
      simpa [ξ] using orderOf_omegaSChar_column_base hG mp tp]
    exact Nat.coprime_comm.mp (tp.p_prime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj0) j.isLt))
  obtain ⟨u, hu, -⟩ :=
    (tiCyclicW hG mp tp).exists_mapRingEquiv_sigma_omega_pow rfl
      (tiCyclicWDadeApp hG mp tp) ξ hjcop
  refine ⟨u, ?_⟩
  rw [tau3W_omegaS_eq_sigma_omegaSChar, tau3W_omegaS_eq_sigma_omegaSChar]
  rw [omegaSChar_column_eq_pow hG mp tp j]
  convert hu.symm using 1
  all_goals simp [ξ]
  all_goals rfl

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.9.b), vanishing transport along the row** (issue-2036 supply):
if the `η₁₀`-value vanishes at `x`, so do all nonprincipal row-axis values.  This is the
pointwise zero consequence of `tau3W_omegaS_row_galois_orbit`. -/
theorem tau3W_omegaS_row_vanish_of_one_zero {x : G}
    (h0 : tau3W hG mp tp
      (omegaS hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩) x = 0)
    (i : Fin tp.q) (hi : i ≠ ⟨0, tp.q_prime.pos⟩) :
    tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) x = 0 := by
  obtain ⟨u, hu⟩ := tau3W_omegaS_row_galois_orbit hG mp tp i hi
  have hv := congrArg (fun f : ClassFunction G ℂ => f x) hu
  simp only [OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_apply, h0, map_zero] at hv
  exact hv.symm

end Section16CharacterData

end

end OddOrder

-- ===== OddOrder/FeitThompson.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

/-- **Peterfalvi §13 coherent Dade-grid producer** (`sorry`-free) — *lane-b*
(Peterfalvi §3–§13 coherent grids).  Given the maximal pair and the type-P
structure, constructs the character grids `ω, μ, ν`, the signs `δ, δ'`, the integral
maps, and the induction identities (13.1.d/e).

The mathematically substantive fields are the genuine §13 grid:
* `omega := omegaS` — the shared `ω`-grid, materialized from the certain-type machinery of
  `mp.S` (`certainTypeS`, indexed by `mp.K`, `mp.Kstar` and aligned to `tp.W₁, tp.W₂` via
  `tp.W1_eq_K`/`W2_eq_Kstar`).  `omegaS_eq_omegaT` proves it equals the T-side reconstruction, so
  the single `ω`-field satisfies *both* induction identities;
* `mu := muS`, `nu := nuT`, `delta := deltaS`, `deltaPrime := deltaPrimeT` — the induced
  exceptional characters and signs read off `certainTypeS`/`certainTypeT`'s `columnFamily`;
* `tau3 := tau3W` — the genuine §3.2 Dade σ-integral of the G-internal TI-cyclic structure on
  `W = S ∩ T`, supported on `Ẑ = W \ (W₁ ∪ W₂)` (built from the proven BG Theorem 14.7 TI fact and
  the general §4 Dade producer; `#print axioms` is `sorryAx`-free);
* `mu_definition := muS_definition`, `nu_definition := nuT_definition` — Peterfalvi (13.1.e),
  proven `sorry`-free.

**Vestigial fields** `Sset, Tset, A0S, A0T, tauS, tauT` carry honest placeholders (`∅`, `0`).
These are *not* consumed on the FT critical path: the §13/§16 contradiction in
`Peterfalvi.S16` (`S16_NonExistenceG`) is routed entirely through `eta = τ₃ ∘ ω` (the W-side
Dade grid), never through the S/T-side maximal-coherent isometries `τ_S, τ_T`.  The only
references to `tauS`/`tauT` are the *uncited* coherence-wiring lemmas in `S15_SAndT_Setup`,
which lie off the FT path.  `Hypothesis` itself places no `Prop`
constraint on these six fields, so the placeholders introduce no unsound dependency — they are
genuine values of the right type for fields the formalized contradiction does not read.  (User
decision 2026-06-24, issue 1004: close the producer on the verified-vestigial finding rather
than build the off-path §7 maximal-coherent Dade theory.) -/
noncomputable def section16CharacterData_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) (tp : Section16TypePStructure mp) :
    Section16CharacterData mp tp := by
  -- The grid building blocks carry `[NeZero |certainType{S,T}.W₁|]` (the prime base-index
  -- normalization); discharge both from `|certainTypeS.W₁| = tp.q`, `|certainTypeT.W₁| = tp.p`.
  haveI : NeZero (Nat.card ↥(mp.certainTypeS hG).W1) :=
    ⟨by rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]; exact tp.q_prime.pos.ne'⟩
  haveI : NeZero (Nat.card ↥(mp.certainTypeT hG).W1) :=
    ⟨by rw [Section16CharacterData.cardCertainTypeT_W1 hG mp tp]; exact tp.p_prime.pos.ne'⟩
  exact
    { Sset := ∅
      Tset := ∅
      A0S := ∅
      A0T := ∅
      tauS := 0
      tauT := 0
      omega := Section16CharacterData.omegaS hG mp tp
      mu := Section16CharacterData.muS hG mp tp
      nu := Section16CharacterData.nuT hG mp tp
      delta := Section16CharacterData.deltaS hG mp tp
      deltaPrime := Section16CharacterData.deltaPrimeT hG mp tp
      delta_pm_one :=
        ⟨fun j => ((mp.certainTypeS hG).columnFamily
            (Section16CharacterData.chi2enum hG mp tp j)).sign_eq,
         fun i => ((mp.certainTypeT hG).columnFamily
            (Section16CharacterData.colT hG mp tp i)).sign_eq⟩
      mu_degree_modEq_delta := fun i j => by
        have : NeZero (Nat.card ↥(mp.certainTypeS hG).W1) :=
          ⟨by rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]; exact tp.q_prime.pos.ne'⟩
        obtain ⟨a, ha⟩ := (mp.certainTypeS hG).certainType_degree_modEq
          (Section16CharacterData.chi2enum hG mp tp j) (Section16CharacterData.eqQ hG mp tp i)
        refine ⟨a, ?_⟩
        have hq : (tp.q : ℂ) = (Nat.card ↥(mp.certainTypeS hG).W1 : ℂ) := by
          rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]
        simp only [Section16CharacterData.muS, Section16CharacterData.deltaS, hq]
        exact ha
      delta_zero_eq_one := by
        have : NeZero (Nat.card ↥(mp.certainTypeS hG).W1) :=
          ⟨by rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]; exact tp.q_prime.pos.ne'⟩
        change Section16CharacterData.deltaS hG mp tp ⟨0, tp.p_prime.pos⟩ = 1
        rw [Section16CharacterData.deltaS, Section16CharacterData.chi2enum_zero]
        exact ((mp.certainTypeS hG).certainType_zero_column_anchor).1
      tau3 := Section16CharacterData.tau3W hG mp tp
      mu_definition := Section16CharacterData.muS_definition hG mp tp
      mu_irreducible := fun i j =>
        (((mp.certainTypeS hG).columnFamily (Section16CharacterData.chi2enum hG mp tp j)).mu
          (Section16CharacterData.eqQ hG mp tp i)).isIrreducible
      mu_col_injective := fun j i i' h =>
        (Section16CharacterData.eqQ hG mp tp).injective
          ((((mp.certainTypeS hG).columnFamily
            (Section16CharacterData.chi2enum hG mp tp j)).injective)
            (OddOrder.RepresentationTheory.IrreducibleCharacter.ext h))
      mu_orthonormal := Section16CharacterData.muS_orthonormal hG mp tp
      mu_diff_support := fun i {j k} hj0 hk0 hdeg =>
        Section16CharacterData.muS_diff_support hG mp tp i hj0 hk0 hdeg
      mu_apply_of_not_mem_W2 := fun i j w hwW hwS hw2 =>
        Section16CharacterData.muS_apply_of_not_mem_W2 hG mp tp i j w hwW hwS hw2
      mu_conj := Section16CharacterData.muS_conj hG mp tp
      tau3_omega_conj := Section16CharacterData.tau3W_omegaS_conj hG mp tp
      mu_colSum_eq_induce := fun j => by
        refine ⟨ClassFunction.restrict ((derivedInG mp.S).subgroupOf mp.S)
            (((mp.certainTypeS hG).columnFamily
              (Section16CharacterData.chi2enum hG mp tp j)).mu 0 : ClassFunction ↥mp.S ℂ),
          ?_, ?_, ?_⟩
        · exact (mp.certainTypeS hG).certainTypeRestrict_isIrreducible _
        · calc (∑ i : Fin tp.q, Section16CharacterData.muS hG mp tp i j)
              = ∑ i' : Fin (Nat.card ↥(mp.certainTypeS hG).W1),
                  (((mp.certainTypeS hG).columnFamily
                    (Section16CharacterData.chi2enum hG mp tp j)).mu i' :
                    ClassFunction ↥mp.S ℂ) := by
                simp only [Section16CharacterData.muS]
                exact Equiv.sum_comp (Section16CharacterData.eqQ hG mp tp)
                  (fun i' => (((mp.certainTypeS hG).columnFamily
                    (Section16CharacterData.chi2enum hG mp tp j)).mu i' :
                    ClassFunction ↥mp.S ℂ))
            _ = _ := ((mp.certainTypeS hG).induce_restrict_certainType_eq _).symm
        · intro hjne hsub
          have hχ₂ne : Section16CharacterData.chi2enum hG mp tp j ≠ 1 := by
            rw [← Section16CharacterData.chi2enum_zero hG mp tp]
            exact fun h => hjne ((Section16CharacterData.chi2enum hG mp tp).injective h)
          refine (mp.certainTypeS hG).not_subset_characterKernel_chiRestrict_of_ne_one
            hχ₂ne ?_
          have hseq : ((tp.W2.subgroupOf mp.S).subgroupOf
                ((derivedInG mp.S).subgroupOf mp.S))
              = (((mp.certainTypeS hG).W2).subgroupOf
                ((derivedInG mp.S).subgroupOf mp.S)) := by
            rw [Section16CharacterData.certainTypeS_W2_eq hG mp, tp.W2_eq_Kstar hG]
          exact hseq ▸ hsub
      mu_reducible_dichotomy := Section16CharacterData.muS_reducible_dichotomy hG mp tp
      nu_definition := Section16CharacterData.nuT_definition hG mp tp
      nu_irreducible := Section16CharacterData.nuT_irreducible hG mp tp
      nu_row_injective := Section16CharacterData.nuT_row_injective hG mp tp
      nu_orthonormal := Section16CharacterData.nuT_orthonormal hG mp tp
      nu_degree_modEq_deltaPrime :=
        Section16CharacterData.nuT_degree_modEq_deltaPrime hG mp tp
      deltaPrime_zero_eq_one := Section16CharacterData.deltaPrimeT_zero_eq_one hG mp tp
      nu_rowSum_eq_induce := Section16CharacterData.nuT_rowSum_eq_induce hG mp tp
      nu_reducible_dichotomy := Section16CharacterData.nuT_reducible_dichotomy hG mp tp
      nu_diff_support := Section16CharacterData.nuT_diff_support hG mp tp
      nu_apply_of_not_mem_W1 := Section16CharacterData.nuT_apply_of_not_mem_W1 hG mp tp
      nu_conj := Section16CharacterData.nuT_conj hG mp tp
      tau3_isometry := Section16CharacterData.tau3W_isometry hG mp tp
      tau3_trivial := Section16CharacterData.tau3W_trivial hG mp tp
      tau3_apply_of_regular := fun α w hwW hnot =>
        Section16CharacterData.tau3W_apply_of_regular hG mp tp α w hwW hnot
      tau3_mem_ZIrr := fun _ hz => Section16CharacterData.tau3W_mem_ZIrr hG mp tp hz
      omega_orthonormal := Section16CharacterData.omegaS_inner hG mp tp
      omega_apply_one := Section16CharacterData.omegaS_apply_one hG mp tp
      omega_mem_ZIrr := Section16CharacterData.omegaS_mem_ZIrr hG mp tp
      omega_mul := Section16CharacterData.omegaS_mul hG mp tp
      omega_col_zero_apply_of_mem_W2 :=
        Section16CharacterData.omegaS_col_zero_apply_of_mem_W2 hG mp tp
      omega_row_zero_apply_of_mem_W1 :=
        Section16CharacterData.omegaS_row_zero_apply_of_mem_W1 hG mp tp
      omega_pow_q_of_mem_W1 := Section16CharacterData.omegaS_pow_q_of_mem_W1 hG mp tp
      omega_pow_p_of_mem_W2 := Section16CharacterData.omegaS_pow_p_of_mem_W2 hG mp tp
      eta_complete_vanish := fun χ horth w hwW hnot =>
        Section16CharacterData.tau3W_omegaS_complete_vanish hG mp tp χ horth hwW hnot
      eta_fourcorner_vanish := fun i j hi hj x hx =>
        Section16CharacterData.tau3W_omegaS_fourcorner_vanish hG mp tp i j hi hj (by
          intro hmem
          obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hmem
          obtain ⟨c, hc⟩ := isConj_iff.mp hconj
          exact hx (OddOrder.GroupTheory.mem_conjClassSet.mpr ⟨a, ha, c, hc⟩))
      eta_row_vanish_of_one_zero := fun x h0 i hi =>
        Section16CharacterData.tau3W_omegaS_row_vanish_of_one_zero hG mp tp h0 i hi
      eta_row_galois_orbit :=
        Section16CharacterData.tau3W_omegaS_row_galois_orbit hG mp tp
      eta_column_galois_orbit :=
        Section16CharacterData.tau3W_omegaS_column_galois_orbit hG mp tp
      eta_intCast_of_coprime := fun g hg i j =>
        Section16CharacterData.tau3W_omegaS_intCast_of_coprime hG mp tp i j hg
      eta_pair_of_coprime := fun g hg i j =>
        Section16CharacterData.tau3W_omegaS_pair_of_coprime hG mp tp i j hg
      eta_principal_of_coprime := fun g hg =>
        Section16CharacterData.tau3W_omegaS_principal_of_coprime hG mp tp hg }

/-- **Assembly of `Section16Inputs` from the three lane producers** (`sorry`-free).
Each field of `Section16Inputs` is sourced from exactly one of `mp` / `tp` / `cd`;
the character fields unify because `mp.S, mp.T, tp.W, tp.q, tp.p` are the chosen
witnesses. -/
noncomputable def section16Inputs_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : Section16Inputs G :=
  let mp := section16MaximalPair_of_isMinimalSimpleOdd hG
  let tp := section16TypePStructure_of_isMinimalSimpleOdd hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG) mp
  let cd := section16CharacterData_of_isMinimalSimpleOdd hG mp tp
  { S := mp.S
    T := mp.T
    W1 := tp.W1
    W2 := tp.W2
    W := tp.W
    U := tp.U
    V := tp.V
    S_maximal := mp.S_maximal
    T_maximal := mp.T_maximal
    S_ne_T := mp.S_ne_T
    S_nonI := mp.S_nonI
    T_nonI := mp.T_nonI
    one_typeII := mp.one_typeII
    theorem88_caseB := mp.theorem88_caseB
    W_eq_inter := tp.W_eq_inter
    W_eq_join := tp.W_eq_join
    W1_inf_W2_eq_bot := tp.W1_inf_W2_eq_bot
    W1_commutes_W2 := tp.W1_commutes_W2
    W_cyclic := tp.W_cyclic
    S_deriv_eq_PU := tp.S_deriv_eq_PU
    T_deriv_eq_QV := tp.T_deriv_eq_QV
    V_inf_Q_eq_bot := tp.V_inf_Q_eq_bot
    W2_isComplement_T_deriv := tp.W2_isComplement_T_deriv
    W1_normalizes_U := tp.W1_normalizes_U
    W2_normalizes_V := tp.W2_normalizes_V
    q := tp.q
    p := tp.p
    q_prime := tp.q_prime
    p_prime := tp.p_prime
    q_eq_card_W1 := tp.q_eq_card_W1
    p_eq_card_W2 := tp.p_eq_card_W2
    u := tp.u
    v := tp.v
    c := tp.c
    d := tp.d
    c_eq_card_C := tp.c_eq_card_C
    d_eq_card_D := tp.d_eq_card_D
    card_U_eq_uc := tp.card_U_eq_uc
    card_V_eq_vd := tp.card_V_eq_vd
    Sset := cd.Sset
    Tset := cd.Tset
    A0S := cd.A0S
    A0T := cd.A0T
    tauS := cd.tauS
    tauT := cd.tauT
    omega := cd.omega
    mu := cd.mu
    nu := cd.nu
    delta := cd.delta
    deltaPrime := cd.deltaPrime
    delta_pm_one := cd.delta_pm_one
    mu_degree_modEq_delta := cd.mu_degree_modEq_delta
    delta_zero_eq_one := cd.delta_zero_eq_one
    tau3 := cd.tau3
    mu_definition := cd.mu_definition
    mu_irreducible := cd.mu_irreducible
    mu_col_injective := cd.mu_col_injective
    mu_orthonormal := cd.mu_orthonormal
    mu_diff_support := cd.mu_diff_support
    mu_apply_of_not_mem_W2 := cd.mu_apply_of_not_mem_W2
    mu_conj := cd.mu_conj
    tau3_omega_conj := cd.tau3_omega_conj
    mu_colSum_eq_induce := cd.mu_colSum_eq_induce
    mu_reducible_dichotomy := cd.mu_reducible_dichotomy
    nu_definition := cd.nu_definition
    nu_irreducible := cd.nu_irreducible
    nu_row_injective := cd.nu_row_injective
    nu_orthonormal := cd.nu_orthonormal
    nu_degree_modEq_deltaPrime := cd.nu_degree_modEq_deltaPrime
    deltaPrime_zero_eq_one := cd.deltaPrime_zero_eq_one
    nu_rowSum_eq_induce := cd.nu_rowSum_eq_induce
    nu_reducible_dichotomy := cd.nu_reducible_dichotomy
    nu_diff_support := cd.nu_diff_support
    nu_apply_of_not_mem_W1 := cd.nu_apply_of_not_mem_W1
    nu_conj := cd.nu_conj
    q_lt_p := tp.q_lt_p
    Sdata := tp.Sdata
    Sdata_U_eq := tp.Sdata_U_eq
    Sdata_W1_eq := tp.Sdata_W1_eq
    S_U_commutative := tp.S_U_commutative
    Sdata_W2_eq := tp.Sdata_W2_eq
    tau3_isometry := cd.tau3_isometry
    tau3_trivial := cd.tau3_trivial
    tau3_apply_of_regular := cd.tau3_apply_of_regular
    tau3_mem_ZIrr := cd.tau3_mem_ZIrr
    omega_orthonormal := cd.omega_orthonormal
    omega_apply_one := cd.omega_apply_one
    omega_mem_ZIrr := cd.omega_mem_ZIrr
    omega_mul := cd.omega_mul
    omega_col_zero_apply_of_mem_W2 := cd.omega_col_zero_apply_of_mem_W2
    omega_row_zero_apply_of_mem_W1 := cd.omega_row_zero_apply_of_mem_W1
    omega_pow_q_of_mem_W1 := cd.omega_pow_q_of_mem_W1
    omega_pow_p_of_mem_W2 := cd.omega_pow_p_of_mem_W2
    eta_complete_vanish := cd.eta_complete_vanish
    eta_fourcorner_vanish := cd.eta_fourcorner_vanish
    eta_row_vanish_of_one_zero := cd.eta_row_vanish_of_one_zero
    eta_row_galois_orbit := cd.eta_row_galois_orbit
    eta_column_galois_orbit := cd.eta_column_galois_orbit
    eta_intCast_of_coprime := cd.eta_intCast_of_coprime
    eta_pair_of_coprime := cd.eta_pair_of_coprime
    eta_principal_of_coprime := cd.eta_principal_of_coprime }

/-- **Assembly of the Section 16 configuration from named inputs** (`sorry`-free).

Given the `Section16Inputs` witnesses, this builds `Peterfalvi.S16.Hypothesis`
without any `sorry`.  Beyond carrying the input fields, it *derives* the fields of
`Peterfalvi.S15.Hypothesis` that are not independent data:

* `finiteG` from the ambient `[Finite G]`;
* the Fitting kernels `P := F(S)`, `Q := F(T)` (`maxNilpotentNormalHall`) and the
  centralizer complements `C := U ∩ C_G(P)`, `D := V ∩ C_G(Q)` definitionally, so
  `P_eq_SF`, `Q_eq_TF`, `C_eq`, `D_eq` are `rfl` — they are determined by
  `S, T, U, V`, not separate data;
* `q_odd`, `p_odd` from `Odd |G|` (subgroup orders divide `|G|`);
* `eta := τ₃ ∘ ω`, discharging **Peterfalvi (13.1.d)** `η_{ij} = ω_{ij}^{τ₃}`
  definitionally — `η` is the τ₃-image of the `ω`-grid, not separate data;
* `m` as the **(13.10)/(13.11)** rational formula in `p, q`, with `m_eq` by `rfl`.

These derivations are why `Section16Inputs` is a *strictly smaller* obligation
than `Peterfalvi.S16.Hypothesis`: discharging the menu does not require separately
producing `P, Q, C, D`, `η`, `m`, or the oddness facts. -/
noncomputable def sectionSixteenHypothesis_of_inputs {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (inp : Section16Inputs G) :
    Peterfalvi.S16.Hypothesis (G := G) where
  base :=
    { S := inp.S
      T := inp.T
      W1 := inp.W1
      W2 := inp.W2
      W := inp.W
      P := maxNilpotentNormalHall inp.S
      Q := maxNilpotentNormalHall inp.T
      U := inp.U
      V := inp.V
      C := inp.U ⊓ Subgroup.centralizer (maxNilpotentNormalHall inp.S : Set G)
      D := inp.V ⊓ Subgroup.centralizer (maxNilpotentNormalHall inp.T : Set G)
      S_maximal := inp.S_maximal
      T_maximal := inp.T_maximal
      S_ne_T := inp.S_ne_T
      S_nonI := inp.S_nonI
      T_nonI := inp.T_nonI
      one_typeII := inp.one_typeII
      theorem88_caseB := inp.theorem88_caseB
      W_eq_inter := inp.W_eq_inter
      W_eq_join := inp.W_eq_join
      W1_inf_W2_eq_bot := inp.W1_inf_W2_eq_bot
      W1_commutes_W2 := inp.W1_commutes_W2
      W_cyclic := inp.W_cyclic
      P_eq_SF := rfl
      Q_eq_TF := rfl
      S_deriv_eq_PU := inp.S_deriv_eq_PU
      T_deriv_eq_QV := inp.T_deriv_eq_QV
      Q_inf_V_eq_bot := inp.V_inf_Q_eq_bot
      W2_isComplement_T_deriv := inp.W2_isComplement_T_deriv
      C_eq := rfl
      D_eq := rfl
      W1_normalizes_U := inp.W1_normalizes_U
      W2_normalizes_V := inp.W2_normalizes_V
      q := inp.q
      p := inp.p
      q_prime := inp.q_prime
      p_prime := inp.p_prime
      q_odd := by
        rw [inp.q_eq_card_W1]
        exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card inp.W1)
      p_odd := by
        rw [inp.p_eq_card_W2]
        exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card inp.W2)
      q_eq_card_W1 := inp.q_eq_card_W1
      p_eq_card_W2 := inp.p_eq_card_W2
      u := inp.u
      v := inp.v
      c := inp.c
      d := inp.d
      c_eq_card_C := inp.c_eq_card_C
      d_eq_card_D := inp.d_eq_card_D
      card_U_eq_uc := inp.card_U_eq_uc
      card_V_eq_vd := inp.card_V_eq_vd
      Sset := inp.Sset
      Tset := inp.Tset
      A0S := inp.A0S
      A0T := inp.A0T
      tauS := inp.tauS
      tauT := inp.tauT
      omega := inp.omega
      eta := fun i j => inp.tau3 (inp.omega i j)
      mu := inp.mu
      nu := inp.nu
      delta := inp.delta
      deltaPrime := inp.deltaPrime
      delta_pm_one := inp.delta_pm_one
      mu_degree_modEq_delta := inp.mu_degree_modEq_delta
      delta_zero_eq_one := inp.delta_zero_eq_one
      tau3 := inp.tau3
      eta_eq_tau_omega := fun _ _ => rfl
      mu_definition := inp.mu_definition
      mu_irreducible := inp.mu_irreducible
      mu_col_injective := inp.mu_col_injective
      mu_orthonormal := inp.mu_orthonormal
      mu_diff_support := inp.mu_diff_support
      mu_apply_of_not_mem_W2 := inp.mu_apply_of_not_mem_W2
      mu_conj := inp.mu_conj
      eta_conj := inp.tau3_omega_conj
      mu_colSum_eq_induce := inp.mu_colSum_eq_induce
      mu_reducible_dichotomy := inp.mu_reducible_dichotomy
      nu_definition := inp.nu_definition
      m := 1 - 1 / ((inp.q : ℚ) - 1) - ((inp.q : ℚ) - 1) / (inp.q : ℚ) ^ inp.p +
        1 / (((inp.q : ℚ) - 1) * (inp.q : ℚ) ^ inp.p)
      m_eq := rfl
      Sdata := inp.Sdata
      Sdata_U_eq := inp.Sdata_U_eq
      Sdata_W1_eq := inp.Sdata_W1_eq
      S_U_commutative := inp.S_U_commutative
      Sdata_W2_eq := inp.Sdata_W2_eq
      tau3_isometry := inp.tau3_isometry
      tau3_trivial := inp.tau3_trivial
      tau3_apply_of_regular := inp.tau3_apply_of_regular
      tau3_mem_ZIrr := inp.tau3_mem_ZIrr
      omega_orthonormal := inp.omega_orthonormal
      omega_apply_one := inp.omega_apply_one
      omega_mem_ZIrr := inp.omega_mem_ZIrr
      omega_mul := inp.omega_mul
      omega_col_zero_apply_of_mem_W2 := inp.omega_col_zero_apply_of_mem_W2
      omega_row_zero_apply_of_mem_W1 := inp.omega_row_zero_apply_of_mem_W1
      omega_pow_q_of_mem_W1 := inp.omega_pow_q_of_mem_W1
      omega_pow_p_of_mem_W2 := inp.omega_pow_p_of_mem_W2
      eta_complete_vanish := inp.eta_complete_vanish
      eta_fourcorner_vanish := inp.eta_fourcorner_vanish
      eta_row_vanish_of_one_zero := inp.eta_row_vanish_of_one_zero
      eta_row_galois_orbit := inp.eta_row_galois_orbit
      eta_column_galois_orbit := inp.eta_column_galois_orbit
      eta_intCast_of_coprime := inp.eta_intCast_of_coprime
      eta_pair_of_coprime := inp.eta_pair_of_coprime
      eta_principal_of_coprime := inp.eta_principal_of_coprime }
  nuGridSupply :=
    { nu_irreducible := inp.nu_irreducible
      nu_row_injective := inp.nu_row_injective
      nu_orthonormal := inp.nu_orthonormal
      nu_degree_modEq_deltaPrime := inp.nu_degree_modEq_deltaPrime
      deltaPrime_zero_eq_one := inp.deltaPrime_zero_eq_one
      nu_rowSum_eq_induce := inp.nu_rowSum_eq_induce
      nu_reducible_dichotomy := inp.nu_reducible_dichotomy
      nu_diff_support := inp.nu_diff_support
      nu_apply_of_not_mem_W1 := inp.nu_apply_of_not_mem_W1
      nu_conj := inp.nu_conj }
  q_lt_p := inp.q_lt_p

/-- **Canonical Section 16 configuration from a minimal simple odd-order group.**
The named Bender–Glauberman and Peterfalvi producers construct
`Section16Inputs G`, and the axiom-clean `sectionSixteenHypothesis_of_inputs`
assembles those inputs into the field-normalizer configuration of Peterfalvi (14.2).

Axiom audit (2026-07-15): this definition and
`section16Inputs_of_isMinimalSimpleOdd` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.  In particular, the former gated input-menu
obligation is no longer the FT frontier.

The downstream `noMinimalSimpleOdd_of_section16` bridge, BG Appendix C final contradiction,
and `feitThompson` have now been audited against the same standard-three-axiom boundary. -/
noncomputable def sectionSixteenHypothesis_of_isMinimalSimpleOdd
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) :
    Peterfalvi.S16.Hypothesis (G := G) :=
  sectionSixteenHypothesis_of_inputs hG.odd (section16Inputs_of_isMinimalSimpleOdd hG)

end

/-- **No minimal simple group of odd order exists.** Combining the upstream
construction of the Section 16 configuration
(`sectionSixteenHypothesis_of_isMinimalSimpleOdd`) with the already-formalized
final contradiction (`noMinimalSimpleOdd_of_section16`). -/
theorem noMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : False :=
  noMinimalSimpleOdd_of_section16 hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG)
    (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
    (sectionSixteenHypothesis_of_isMinimalSimpleOdd hG)

/-- **Minimal-counterexample reduction** (pure group theory, `sorry`-free).

If no minimal simple group of odd order exists, then every finite group of odd
order is solvable.

The proof is strong induction on `Nat.card G`. If `G` were a non-solvable group of
odd order, then — using the induction hypothesis on its (smaller, odd-order) proper
subgroups and proper quotients — every proper subgroup is solvable and `G` is
simple: a proper nontrivial normal subgroup `N` would make `G` an extension of the
solvable group `N` by the solvable group `G ⧸ N`, hence solvable
(`Group.isSolvable_of_ker_le_range`). Thus `G` would be a minimal simple group of odd
order, contradicting the hypothesis `hno`. -/
theorem feitThompson_of_noMinimalSimpleOdd
    (hno : ∀ (H : Type u) [Group H] [Finite H], IsMinimalSimpleOdd H → False)
    {G : Type u} [Group G] [Finite G] (hodd : Odd (Nat.card G)) :
    Group.IsSolvable G := by
  -- Strong induction on the order, generalized over all groups in this universe.
  suffices key : ∀ (n : ℕ) (K : Type u) [Group K] [Finite K],
      Nat.card K = n → Odd (Nat.card K) → Group.IsSolvable K from key (Nat.card G) G rfl hodd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ hcard hodd'
    subst hcard
    by_contra hns
    -- `K` is nontrivial: a subsingleton group is solvable.
    have hNT : Nontrivial K := by
      by_contra hc
      rw [not_nontrivial_iff_subsingleton] at hc
      have := hc
      exact hns inferInstance
    -- `K` is simple: a proper nontrivial normal subgroup splits `K` as a solvable
    -- extension of a solvable group, making `K` solvable.
    have hsimple : IsSimpleGroup K := by
      refine { toNontrivial := hNT, eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨hNbot, hNtop⟩ := hcon
      -- `N` is solvable (proper subgroup of odd order, induction hypothesis).
      have hN_odd : Odd (Nat.card ↥N) :=
        hodd'.of_dvd_nat (Subgroup.card_subgroup_dvd_card N)
      have hNlt : Nat.card ↥N < Nat.card K := by
        have hidx : 1 < N.index := Subgroup.one_lt_index_of_ne_top hNtop
        have h := lt_mul_of_one_lt_right (Nat.card_pos (α := ↥N)) hidx
        rwa [Subgroup.card_mul_index] at h
      have : Group.IsSolvable ↥N := ih (Nat.card ↥N) hNlt ↥N rfl hN_odd
      -- `K ⧸ N` is solvable (proper quotient of odd order, induction hypothesis).
      have hQ_odd : Odd (Nat.card (K ⧸ N)) :=
        hodd'.of_dvd_nat (Subgroup.card_quotient_dvd_card N)
      have hQlt : Nat.card (K ⧸ N) < Nat.card K := by
        have hN1 : 1 < Nat.card ↥N :=
          Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot N).mpr hNbot)
        have h := lt_mul_of_one_lt_right (Nat.card_pos (α := K ⧸ N)) hN1
        rwa [← Subgroup.card_eq_card_quotient_mul_card_subgroup] at h
      have : Group.IsSolvable (K ⧸ N) := ih (Nat.card (K ⧸ N)) hQlt (K ⧸ N) rfl hQ_odd
      -- Extension of a solvable group by a solvable group is solvable.
      have hfg : (QuotientGroup.mk' N).ker ≤ (N.subtype).range :=
        le_of_eq ((QuotientGroup.ker_mk' N).trans (Subgroup.subtype_range N).symm)
      exact hns (Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) hfg)
    -- Every proper subgroup is solvable (smaller, odd order, induction hypothesis).
    have hproper : ∀ M : Subgroup K, M < ⊤ → Group.IsSolvable ↥M := by
      intro M hM
      have hM_odd : Odd (Nat.card ↥M) :=
        hodd'.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
      have hMlt : Nat.card ↥M < Nat.card K := by
        have hidx : 1 < M.index := Subgroup.one_lt_index_of_ne_top (ne_of_lt hM)
        have h := lt_mul_of_one_lt_right (Nat.card_pos (α := ↥M)) hidx
        rwa [Subgroup.card_mul_index] at h
      exact ih (Nat.card ↥M) hMlt ↥M rfl hM_odd
    -- `K` is then a minimal simple group of odd order — impossible.
    exact hno K ⟨hodd', hsimple, hns, hproper⟩

/-- **Feit-Thompson theorem**: every finite group of odd order is solvable.

This combines the `sorry`-free minimal-counterexample reduction
(`feitThompson_of_noMinimalSimpleOdd`) with the non-existence of a minimal simple
group of odd order (`noMinimalSimpleOdd`).  The complete theorem is axiom-clean:
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. -/
theorem _root_.solution {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) :
    Group.IsSolvable G :=
  feitThompson_of_noMinimalSimpleOdd (fun _ _ _ hG => noMinimalSimpleOdd hG) hodd

end OddOrder
