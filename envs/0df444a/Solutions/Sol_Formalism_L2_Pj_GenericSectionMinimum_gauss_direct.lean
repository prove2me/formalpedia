-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.gauss_direct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:23:06.854032+00:00
-- url     : https://prove2.me/submissions/8fb847cf-31e9-48f2-8fe3-933772ba804d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_kill_adjoin
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_algIndep_of_der
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_gauss_indep
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_residueTrdeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open IsLocalRing Cardinal
namespace Formalism.L2.Pj.GenericSectionMinimum
theorem _root_.solution {F K : Type} [Field F] [Field K] [CharZero K] [Algebra K F] (D N : ℕ)
    (T : Fin (D + 1) × Fin N → F) (y : Fin N → F) (δ : Fin N → F → F) (hδ : ∀ l, IsDer (δ l))
    (hδK : ∀ l c, δ l (algebraMap K F c) = 0) (hδ0 : ∀ l k, δ l (T (0, k)) = if k = l then 1 else 0)
    (hδs : ∀ l (i : Fin D) k, δ l (T (i.succ, k)) = 0) (hδy : ∀ l k, δ l (y k) = -(y k * y l))
    (h1 : ∑ k, T (0, k) * y k = 1)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range T)) F)
    (V : ValuationSubring F)
    (hG : ∀ Q : MvPolynomial (Fin (D + 1) × Fin N) K, (∀ α, V.valuation (algebraMap K F (Q.coeff α)) ≤ 1) →
      (∃ α, V.valuation (algebraMap K F (Q.coeff α)) = 1) → V.valuation (MvPolynomial.aeval T Q) = 1) :
    ∀ k, y k ∈ V := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

  have hT1 : ∀ q, V.valuation (T q) = 1 := by
    intro q
    have := hG (MvPolynomial.X q) (fun α => ?_) ⟨Finsupp.single q 1, ?_⟩
    · simpa using this
    · rw [MvPolynomial.coeff_X']
      split_ifs <;> simp
    · rw [MvPolynomial.coeff_X', if_pos rfl]
      simp
  have hTV : ∀ q, T q ∈ V := fun q => (V.valuation_le_one_iff _).1 (hT1 q).le

  have hTind : AlgebraicIndependent K T := by
    rw [algebraicIndependent_iff]
    intro Q hQ
    by_contra hQ0
    have hne : Q.support.Nonempty := by
      obtain ⟨β, hβ⟩ := MvPolynomial.ne_zero_iff.mp hQ0
      exact ⟨β, MvPolynomial.mem_support_iff.mpr hβ⟩
    obtain ⟨α, hα, hmax⟩ := Q.support.exists_max_image (fun β => V.valuation (algebraMap K F (Q.coeff β))) hne
    have hc : Q.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
    have hvc : V.valuation (algebraMap K F (Q.coeff α)) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]
      exact (map_ne_zero _).2 hc
    have key := hG (MvPolynomial.C (Q.coeff α)⁻¹ * Q) (fun β => ?_) ⟨α, ?_⟩
    · rw [map_mul, hQ, mul_zero, Valuation.map_zero] at key
      exact zero_ne_one key
    · rw [MvPolynomial.coeff_C_mul, map_mul, Valuation.map_mul, map_inv₀, Valuation.map_inv]
      by_cases hβ : β ∈ Q.support
      · calc (V.valuation (algebraMap K F (Q.coeff α)))⁻¹ * V.valuation (algebraMap K F (Q.coeff β))
            ≤ (V.valuation (algebraMap K F (Q.coeff α)))⁻¹ * V.valuation (algebraMap K F (Q.coeff α)) :=
              by gcongr; exact hmax β hβ
          _ = 1 := inv_mul_cancel₀ hvc
      · rw [MvPolynomial.notMem_support_iff.mp hβ, map_zero, Valuation.map_zero, mul_zero]
        exact zero_le'
    · rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, map_one, Valuation.map_one]

  have hN : ∃ k, y k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at h1
  obtain ⟨j0, -, hj0⟩ := Finset.univ.exists_max_image (fun k => V.valuation (y k))
    (by obtain ⟨k, -⟩ := hN; exact ⟨k, Finset.mem_univ _⟩)
  have hy0 : y j0 ≠ 0 := by
    obtain ⟨k, hk⟩ := hN
    intro h0
    have := hj0 k (Finset.mem_univ _)
    rw [h0, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hk this
  let a : Fin N → F := fun k => y k / y j0
  have haV : ∀ k, V.valuation (a k) ≤ 1 := by
    intro k
    show V.valuation (y k / y j0) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ (hj0 k (Finset.mem_univ _)) zero_le'
  have ha0 : a j0 = 1 := div_self hy0
  have hay : ∀ k, a k * y j0 = y k := fun k => div_mul_cancel₀ _ hy0
  have hδa : ∀ l k, δ l (a k) = 0 := by
    intro l k
    have e := (hδ l).mul (a k) (y j0)
    rw [hay, hδy, hδy] at e
    have e2 : y j0 * δ l (a k) = 0 := by linear_combination (-1 : F) * e + y l * hay k
    exact (mul_eq_zero.mp e2).resolve_left hy0

  let sE : Set F := Set.range (fun q : Fin D × Fin N => T (q.1.succ, q.2)) ∪ Set.range a
  let E : IntermediateField K F := IntermediateField.adjoin K sE
  have hδE : ∀ l (e : E), δ l (algebraMap E F e) = 0 := by
    intro l e
    show δ l (e : F) = 0
    refine kill_adjoin K (hδ l) (hδK l) sE ?_ e e.2
    rintro x (⟨q, rfl⟩ | ⟨k, rfl⟩)
    · exact hδs l q.1 q.2
    · exact hδa l k
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hT0ind : AlgebraicIndependent E (fun k => T (0, k)) :=
    algIndep_of_der _ δ hδ hδE (fun l k => hδ0 l k)

  have hmemT : ∀ (i : Fin D) k, T (i.succ, k) ∈ E := fun i k =>
    IntermediateField.subset_adjoin K sE (Set.mem_union_left _ ⟨(i, k), rfl⟩)
  have hmema : ∀ k, a k ∈ E := fun k =>
    IntermediateField.subset_adjoin K sE (Set.mem_union_right _ ⟨k, rfl⟩)
  haveI : FaithfulSMul K E := (faithfulSMul_iff_algebraMap_injective K E).mpr (algebraMap K E).injective
  haveI : FaithfulSMul E F := (faithfulSMul_iff_algebraMap_injective E F).mpr (algebraMap E F).injective
  have hadd : Algebra.trdeg K E + Algebra.trdeg E F ≤ Algebra.trdeg K F := trdeg_add_le
  have htF : Algebra.trdeg K F ≤ (((D + 1) * N : ℕ) : Cardinal) := by
    haveI := halg
    calc Algebra.trdeg K F ≤ #(Set.range T) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range T)
      _ ≤ #(Fin (D + 1) × Fin N) := Cardinal.mk_range_le
      _ = (((D + 1) * N : ℕ) : Cardinal) := by simp [Cardinal.mk_fintype]
  have hEF : ((N : ℕ) : Cardinal) ≤ Algebra.trdeg E F := by
    simpa using hT0ind.cardinalMk_le_trdeg
  let t' : Fin D × Fin N → E := fun q => ⟨T (q.1.succ, q.2), hmemT q.1 q.2⟩
  have ht' : AlgebraicIndependent K t' := by
    have hinj : Function.Injective (fun q : Fin D × Fin N => ((q.1.succ, q.2) : Fin (D + 1) × Fin N)) := by
      intro u v huv
      have h' : ((u.1.succ, u.2) : Fin (D + 1) × Fin N) = (v.1.succ, v.2) := huv
      obtain ⟨h1', h2'⟩ := Prod.mk.inj h'
      exact Prod.ext_iff.2 ⟨Fin.succ_injective _ h1', h2'⟩
    exact AlgebraicIndependent.of_comp E.val (hTind.comp _ hinj)
  have hlow : (((D * N : ℕ)) : Cardinal) ≤ Algebra.trdeg K E := by
    simpa using ht'.cardinalMk_le_trdeg
  have hfin : Algebra.trdeg K E < ℵ₀ :=
    lt_of_le_of_lt (le_self_add.trans ((add_le_add le_rfl hEF).trans (hadd.trans htF)))
      Cardinal.natCast_lt_aleph0
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 hfin
  have hle : n + N ≤ (D + 1) * N := by
    have := (add_le_add le_rfl hEF).trans (hadd.trans htF)
    rw [hn] at this
    exact_mod_cast this
  have hge : D * N ≤ n := by
    rw [hn] at hlow
    exact_mod_cast hlow
  have htr : Algebra.trdeg K E = ((D * N : ℕ) : Cardinal) := by
    rw [hn]
    congr 1
    have e : (D + 1) * N = D * N + N := by ring
    rw [e] at hle
    exact le_antisymm (Nat.le_of_add_le_add_right hle) hge

  let u : Fin (D + 1) × Fin N → V := fun q => ⟨T q, hTV q⟩
  let p : Fin (D + 1) × Fin N → MvPolynomial (Fin N) E := fun q =>
    Fin.cases (motive := fun _ => MvPolynomial (Fin N) E) (MvPolynomial.X q.2)
      (fun i => MvPolynomial.C (⟨T (i.succ, q.2), hmemT i q.2⟩ : E)) q.1
  have hp : ∀ q α, (p q).coeff α ∈ V.comap (algebraMap E F) := by
    rintro ⟨i, k⟩ α
    induction i using Fin.cases with
    | zero =>
      show (MvPolynomial.X k : MvPolynomial (Fin N) E).coeff α ∈ V.comap (algebraMap E F)
      rw [MvPolynomial.coeff_X']
      split_ifs
      · exact (V.comap (algebraMap E F)).one_mem
      · exact (V.comap (algebraMap E F)).zero_mem
    | succ i =>
      show (MvPolynomial.C (⟨T (i.succ, k), hmemT i k⟩ : E)).coeff α ∈ V.comap (algebraMap E F)
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact hTV _
      · exact (V.comap (algebraMap E F)).zero_mem
  have hpu : ∀ q, MvPolynomial.aeval (fun s => T (0, s)) (p q) = (u q : F) := by
    rintro ⟨i, k⟩
    induction i using Fin.cases with
    | zero =>
      show MvPolynomial.aeval (fun s => T (0, s)) (MvPolynomial.X k : MvPolynomial (Fin N) E) = T (0, k)
      rw [MvPolynomial.aeval_X]
    | succ i =>
      show MvPolynomial.aeval (fun s => T (0, s)) (MvPolynomial.C (⟨T (i.succ, k), hmemT i k⟩ : E)) = T (i.succ, k)
      rw [MvPolynomial.aeval_C]
      rfl
  have hcard : Fintype.card (Fin (D + 1) × Fin N) = Fintype.card (Fin N) + D * N := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  have hind := gauss_indep (Ω := E) V T hTV hG
  have RT := ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K E F (D * N) htr (Fin N) (fun s => T (0, s)) V
    (fun s => hTV _) (Fin (D + 1) × Fin N) u p hp hcard hpu hind
  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap E F)
  have RT3 := RT.2.2

  have haW : ∀ k, (⟨a k, hmema k⟩ : E) ∈ V.comap (algebraMap E F) := fun k =>
    (V.valuation_le_one_iff _).1 (haV k)
  let abar : Fin N → ResidueField (V.comap (algebraMap E F)) := fun k => residue (V.comap (algebraMap E F)) ⟨⟨a k, hmema k⟩, haW k⟩
  let aV : Fin N → V := fun k => ⟨a k, (V.valuation_le_one_iff _).1 (haV k)⟩
  let tV : Fin N → V := fun k => ⟨T (0, k), hTV _⟩
  let Lp : MvPolynomial (Fin N) (ResidueField (V.comap (algebraMap E F))) :=
    ∑ k, MvPolynomial.C (abar k) * MvPolynomial.X k
  have hLp : Lp ≠ 0 := by
    intro h0
    have := congrArg (fun P => MvPolynomial.coeff (Finsupp.single j0 1) P) h0
    simp only [Lp, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
      MvPolynomial.coeff_zero] at this
    rw [Finset.sum_eq_single j0] at this
    · rw [if_pos rfl, mul_one] at this
      have h1' : abar j0 = 1 := by
        show residue (V.comap (algebraMap E F)) ⟨⟨a j0, hmema j0⟩, haW j0⟩ = 1
        have : (⟨⟨a j0, hmema j0⟩, haW j0⟩ : ↥(V.comap (algebraMap E F))) = 1 := Subtype.ext (Subtype.ext ha0)
        rw [this, map_one]
      rw [h1'] at this
      exact one_ne_zero this
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hs
      exact hb ((Finsupp.single_left_inj one_ne_zero).mp hs)
    · simp
  have hev : MvPolynomial.aeval (fun s => residue V ⟨T (0, s), hTV _⟩) Lp = residue V (∑ k, aV k * tV k) := by
    simp only [Lp, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
  have hres : residue V (∑ k, aV k * tV k) ≠ 0 := by
    rw [← hev]
    intro h0
    exact hLp (RT3.eq_zero_of_aeval_eq_zero _ h0)
  have hunit : IsUnit (∑ k, aV k * tV k) := by
    by_contra hnu
    apply hres
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hnu
  have hL1 : V.valuation (∑ k, a k * T (0, k)) = 1 := by
    have := (V.valuation_eq_one_iff _).1 hunit
    simpa [aV, tV] using this

  have hprod : y j0 * ∑ k, a k * T (0, k) = 1 := by
    rw [Finset.mul_sum, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hay k]
    ring
  have hyv : V.valuation (y j0) = 1 := by
    have := congrArg V.valuation hprod
    rw [Valuation.map_mul, hL1, mul_one, Valuation.map_one] at this
    exact this
  intro k
  rw [← V.valuation_le_one_iff]
  exact (hj0 k (Finset.mem_univ _)).trans hyv.le
end Formalism.L2.Pj.GenericSectionMinimum
