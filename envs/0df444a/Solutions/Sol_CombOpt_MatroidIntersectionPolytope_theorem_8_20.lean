-- Prove2me | solution 1 for CombOpt.MatroidIntersectionPolytope.theorem_8_20
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T06:22:07.442205+00:00
-- url     : https://prove2.me/submissions/44c6e2c2-a211-4fb3-b03a-7286de6f7386

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank
import Definitions.Def_CombOpt_TJoin_charVec
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_intersectionLP

set_option autoImplicit false

namespace MIPAux
open CombOpt.MatroidIntersectionPolytope CombOpt.TJoin

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma card_le_rank (M : FinMatroid S) {A J : Finset S} (hJA : J ⊆ A) (hJ : M.Indep J) :
    J.card ≤ rank M A := by
  classical
  unfold rank
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hJA, hJ⟩)

lemma exists_rank_attain (M : FinMatroid S) (A : Finset S) :
    ∃ J, J ⊆ A ∧ M.Indep J ∧ J.card = rank M A := by
  classical
  have hne : (A.powerset.filter M.Indep).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, M.indep_empty⟩⟩
  obtain ⟨Js, hJsmem, hJseq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hJsmem
  refine ⟨Js, hJsmem.1, hJsmem.2, ?_⟩
  unfold rank
  rw [hJseq]

lemma rank_le_card (M : FinMatroid S) (A : Finset S) : rank M A ≤ A.card := by
  obtain ⟨J, hJA, -, hJ⟩ := exists_rank_attain M A
  rw [← hJ]; exact Finset.card_le_card hJA

lemma indep_of_card_le_rank (M : FinMatroid S) {A : Finset S} (h : A.card ≤ rank M A) :
    M.Indep A := by
  obtain ⟨J, hJA, hJI, hJ⟩ := exists_rank_attain M A
  have : J = A := Finset.eq_of_subset_of_card_le hJA (by omega)
  rw [← this]; exact hJI

lemma exists_extend (M : FinMatroid S) {A J₀ : Finset S} (hA : J₀ ⊆ A) (hJ₀ : M.Indep J₀) :
    ∃ J, J₀ ⊆ J ∧ J ⊆ A ∧ M.Indep J ∧ rank M A ≤ J.card := by
  classical
  obtain ⟨J, hJmem, hJmax⟩ :=
    (A.powerset.filter (fun J => M.Indep J ∧ J₀ ⊆ J)).exists_max_image Finset.card
      ⟨J₀, by simp [hA, hJ₀]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hJmem
  obtain ⟨hJA, hJI, hJ₀J⟩ := hJmem
  obtain ⟨Js, hJsA, hJsI, hJseq⟩ := exists_rank_attain M A
  have hbJ : J ⊆ A ∧ M.Indep J ∧ ∀ J', J ⊆ J' → J' ⊆ A → M.Indep J' → J' = J := by
    refine ⟨hJA, hJI, fun J' hJJ' hJ'A hJ'I => ?_⟩
    have hle : J'.card ≤ J.card :=
      hJmax J' (by simp [hJ'A, hJ'I, hJ₀J.trans hJJ'])
    exact (Finset.eq_of_subset_of_card_le hJJ' hle).symm
  have hbJs : Js ⊆ A ∧ M.Indep Js ∧ ∀ J', Js ⊆ J' → J' ⊆ A → M.Indep J' → J' = Js := by
    refine ⟨hJsA, hJsI, fun J' hJJ' hJ'A hJ'I => ?_⟩
    have hle : J'.card ≤ Js.card := by
      rw [hJseq]; exact card_le_rank M hJ'A hJ'I
    exact (Finset.eq_of_subset_of_card_le hJJ' hle).symm
  refine ⟨J, hJ₀J, hJA, hJI, ?_⟩
  rw [← hJseq, M.maximal_card_eq A J Js hbJ hbJs]

lemma rank_submod (M : FinMatroid S) (A B : Finset S) :
    rank M (A ∩ B) + rank M (A ∪ B) ≤ rank M A + rank M B := by
  obtain ⟨I, -, hIs, hII, hIr⟩ := exists_extend M (Finset.empty_subset (A ∩ B)) M.indep_empty
  obtain ⟨J, hIJ, hJs, hJI, hJr⟩ :=
    exists_extend M (hIs.trans (Finset.inter_subset_union : A ∩ B ⊆ A ∪ B)) hII
  have hA : (J ∩ A).card ≤ rank M A :=
    card_le_rank M Finset.inter_subset_right (M.indep_subset J _ Finset.inter_subset_left hJI)
  have hB : (J ∩ B).card ≤ rank M B :=
    card_le_rank M Finset.inter_subset_right (M.indep_subset J _ Finset.inter_subset_left hJI)
  have hU : (J ∩ A) ∪ (J ∩ B) = J := by
    rw [← Finset.inter_union_distrib_left]; exact Finset.inter_eq_left.2 hJs
  have hI : I ⊆ (J ∩ A) ∩ (J ∩ B) := by
    intro e he
    have h1 := hIs he
    rw [Finset.mem_inter] at h1
    simp [hIJ he, h1.1, h1.2]
  have hc := Finset.card_union_add_card_inter (J ∩ A) (J ∩ B)
  rw [hU] at hc
  have := Finset.card_le_card hI
  omega

lemma sum_charVec (J A : Finset S) : ∑ e ∈ A, charVec J e = ((A ∩ J).card : ℝ) := by
  simp only [charVec]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]

lemma charVec_mem (M₁ M₂ : FinMatroid S) {J : Finset S} (h₁ : M₁.Indep J) (h₂ : M₂.Indep J) :
    charVec J ∈ intersectionLP M₁ M₂ := by
  simp only [intersectionLP, Set.mem_ofPred_eq]
  refine ⟨fun A => ?_, fun A => ?_, fun e => ?_⟩
  · rw [sum_charVec]
    exact_mod_cast card_le_rank M₁ Finset.inter_subset_left
      (M₁.indep_subset J _ Finset.inter_subset_right h₁)
  · rw [sum_charVec]
    exact_mod_cast card_le_rank M₂ Finset.inter_subset_left
      (M₂.indep_subset J _ Finset.inter_subset_right h₂)
  · simp only [charVec]; split_ifs <;> norm_num

lemma lp_convex (M₁ M₂ : FinMatroid S) : Convex ℝ (intersectionLP M₁ M₂) := by
  intro x hx y hy a b ha hb hab
  simp only [intersectionLP, Set.mem_ofPred_eq] at hx hy ⊢
  have key : ∀ (A : Finset S) (r : ℝ), ∑ e ∈ A, x e ≤ r → ∑ e ∈ A, y e ≤ r →
      ∑ e ∈ A, (a • x + b • y) e ≤ r := by
    intro A r h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    calc a * ∑ e ∈ A, x e + b * ∑ e ∈ A, y e ≤ a * r + b * r :=
          add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
      _ = r := by rw [← add_mul, hab, one_mul]
  refine ⟨fun A => key A _ (hx.1 A) (hy.1 A), fun A => key A _ (hx.2.1 A) (hy.2.1 A),
    fun e => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx.2.2 e)) (mul_nonneg hb (hy.2.2 e))

lemma le_one_of_mem (M₁ M₂ : FinMatroid S) {x : S → ℝ} (hx : x ∈ intersectionLP M₁ M₂)
    (e : S) : x e ≤ 1 := by
  simp only [intersectionLP, Set.mem_ofPred_eq] at hx
  have h := hx.1 {e}
  rw [Finset.sum_singleton] at h
  have h2 : (rank M₁ {e} : ℝ) ≤ 1 := by
    have := rank_le_card M₁ {e}
    rw [Finset.card_singleton] at this
    exact_mod_cast this
  linarith

lemma lp_compact (M₁ M₂ : FinMatroid S) : IsCompact (intersectionLP M₁ M₂) := by
  have hc : IsClosed (intersectionLP M₁ M₂) := by
    have h1 : ∀ (M : FinMatroid S) (A : Finset S),
        IsClosed {x : S → ℝ | ∑ e ∈ A, x e ≤ (rank M A : ℝ)} := fun M A =>
      isClosed_le (continuous_finsetSum _ fun e _ => continuous_apply e) continuous_const
    have h3 : ∀ e : S, IsClosed {x : S → ℝ | 0 ≤ x e} := fun e =>
      isClosed_le continuous_const (continuous_apply e)
    have : intersectionLP M₁ M₂ = (⋂ A, {x : S → ℝ | ∑ e ∈ A, x e ≤ (rank M₁ A : ℝ)}) ∩
        ((⋂ A, {x : S → ℝ | ∑ e ∈ A, x e ≤ (rank M₂ A : ℝ)}) ∩ ⋂ e, {x : S → ℝ | 0 ≤ x e}) := by
      ext x; simp [intersectionLP]
    rw [this]
    exact (isClosed_iInter (h1 M₁)).inter ((isClosed_iInter (h1 M₂)).inter (isClosed_iInter h3))
  have hb : Bornology.IsBounded (intersectionLP M₁ M₂) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun e => ?_
    rw [Real.norm_eq_abs, abs_le]
    have h0 : 0 ≤ x e := by
      simp only [intersectionLP, Set.mem_ofPred_eq] at hx; exact hx.2.2 e
    exact ⟨by linarith, le_one_of_mem M₁ M₂ hx e⟩
  exact Metric.isCompact_of_isClosed_isBounded hc hb

/-- Glue: Krein–Milman reduces the theorem to the extreme points. -/
lemma glue (M₁ M₂ : FinMatroid S)
    (hext : (intersectionLP M₁ M₂).extremePoints ℝ ⊆
      {x : S → ℝ | ∃ J : Finset S, M₁.Indep J ∧ M₂.Indep J ∧ x = charVec J}) :
    convexHull ℝ {x : S → ℝ | ∃ J : Finset S, M₁.Indep J ∧ M₂.Indep J ∧ x = charVec J} =
      intersectionLP M₁ M₂ := by
  apply le_antisymm
  · refine convexHull_min ?_ (lp_convex M₁ M₂)
    rintro x ⟨J, h1, h2, rfl⟩
    exact charVec_mem M₁ M₂ h1 h2
  · intro x hx
    have hfin : {x : S → ℝ | ∃ J : Finset S, M₁.Indep J ∧ M₂.Indep J ∧ x = charVec J}.Finite :=
      (Set.finite_range (charVec (E := S))).subset (by rintro x ⟨J, -, -, rfl⟩; exact ⟨J, rfl⟩)
    have hcl : IsClosed (convexHull ℝ
        {x : S → ℝ | ∃ J : Finset S, M₁.Indep J ∧ M₂.Indep J ∧ x = charVec J}) :=
      (hfin.isCompact_convexHull (𝕜 := ℝ)).isClosed
    rw [← closure_convexHull_extremePoints (lp_compact M₁ M₂) (lp_convex M₁ M₂)] at hx
    exact closure_minimal (convexHull_mono hext) hcl hx


lemma not_extreme_of_dir (M₁ M₂ : FinMatroid S) {x y : S → ℝ} (hx : x ∈ intersectionLP M₁ M₂)
    (hy0 : y ≠ 0) (hyx : ∀ e, x e = 0 → y e = 0)
    (hT1 : ∀ A : Finset S, ∑ e ∈ A, x e = (rank M₁ A : ℝ) → ∑ e ∈ A, y e = 0)
    (hT2 : ∀ A : Finset S, ∑ e ∈ A, x e = (rank M₂ A : ℝ) → ∑ e ∈ A, y e = 0) :
    x ∉ (intersectionLP M₁ M₂).extremePoints ℝ := by
  have hx' := hx
  simp only [intersectionLP, Set.mem_ofPred_eq] at hx'
  have hcont : ∀ c d : ℝ, Continuous fun t : ℝ => c + t * d := fun c d =>
    continuous_const.add (continuous_id.mul continuous_const)
  have hsum : ∀ (A : Finset S) (t : ℝ),
      ∑ e ∈ A, (x + t • y) e = ∑ e ∈ A, x e + t * ∑ e ∈ A, y e := by
    intro A t; simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hcon : ∀ (M : FinMatroid S), (∀ A, ∑ e ∈ A, x e ≤ (rank M A : ℝ)) →
      (∀ A : Finset S, ∑ e ∈ A, x e = (rank M A : ℝ) → ∑ e ∈ A, y e = 0) →
      ∀ A : Finset S, ∀ᶠ t in nhds (0:ℝ), ∑ e ∈ A, (x + t • y) e ≤ (rank M A : ℝ) := by
    intro M hM hT A
    rcases (hM A).lt_or_eq with hlt | heq
    · have h1 : Filter.Tendsto (fun t : ℝ => ∑ e ∈ A, x e + t * ∑ e ∈ A, y e) (nhds 0)
          (nhds (∑ e ∈ A, x e + 0 * ∑ e ∈ A, y e)) := (hcont _ _).tendsto 0
      rw [zero_mul, add_zero] at h1
      filter_upwards [h1.eventually (gt_mem_nhds hlt)] with t ht
      rw [hsum]; exact ht.le
    · filter_upwards with t
      rw [hsum, hT A heq, mul_zero, add_zero]; exact heq.le
  have hnn : ∀ e, ∀ᶠ t in nhds (0:ℝ), 0 ≤ (x + t • y) e := by
    intro e
    rcases (hx'.2.2 e).lt_or_eq with hlt | heq
    · have h1 : Filter.Tendsto (fun t : ℝ => x e + t * y e) (nhds 0) (nhds (x e + 0 * y e)) :=
        (hcont _ _).tendsto 0
      rw [zero_mul, add_zero] at h1
      filter_upwards [h1.eventually (lt_mem_nhds hlt)] with t ht
      simpa using ht.le
    · filter_upwards with t
      simp [hyx e heq.symm, ← heq]
  have hall : ∀ᶠ t in nhds (0:ℝ), x + t • y ∈ intersectionLP M₁ M₂ := by
    have a1 := Filter.eventually_all.2 (hcon M₁ hx'.1 hT1)
    have a2 := Filter.eventually_all.2 (hcon M₂ hx'.2.1 hT2)
    have a3 := Filter.eventually_all.2 hnn
    filter_upwards [a1, a2, a3] with t h1 h2 h3
    simp only [intersectionLP, Set.mem_ofPred_eq]
    exact ⟨h1, h2, h3⟩
  have hneg : ∀ᶠ t in nhds (0:ℝ), x + (-t) • y ∈ intersectionLP M₁ M₂ := by
    have : Filter.Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg.tendsto (0:ℝ))
    exact this.eventually hall
  obtain ⟨t, ⟨h1, h2⟩, ht0⟩ :=
    (((hall.and hneg).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {(0:ℝ)}ᶜ ∈ nhdsWithin (0:ℝ) {0}ᶜ)).exists
  have ht0' : t ≠ 0 := ht0
  intro hext
  have hseg : x ∈ openSegment ℝ (x + t • y) (x + (-t) • y) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext e; simp; ring
  have h3 := ((mem_extremePoints.1 hext).2 _ h1 _ h2 hseg).1
  have h4 : t • y = 0 := by
    have h := congrArg (fun z => z - x) h3
    simpa using h
  rcases smul_eq_zero.1 h4 with h | h
  · exact ht0' h
  · exact hy0 h

lemma ext_of_01 (M₁ M₂ : FinMatroid S) {x : S → ℝ} (hx : x ∈ intersectionLP M₁ M₂)
    (h01 : ∀ e, x e = 0 ∨ x e = 1) :
    ∃ J : Finset S, M₁.Indep J ∧ M₂.Indep J ∧ x = charVec J := by
  classical
  simp only [intersectionLP, Set.mem_ofPred_eq] at hx
  set J := Finset.univ.filter (fun e => x e = 1) with hJ
  have hxJ : x = charVec J := by
    funext e
    simp only [charVec, hJ, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h01 e with h | h <;> simp [h]
  have hsum : ∑ e ∈ J, x e = (J.card : ℝ) := by
    rw [hxJ, sum_charVec, Finset.inter_self]
  refine ⟨J, indep_of_card_le_rank M₁ ?_, indep_of_card_le_rank M₂ ?_, hxJ⟩
  · have := hx.1 J; rw [hsum] at this; exact_mod_cast this
  · have := hx.2.1 J; rw [hsum] at this; exact_mod_cast this

lemma exists_kernel (F : Finset S) (𝒞 : Finset (Finset S)) (h : 𝒞.card < F.card) :
    ∃ y : S → ℝ, y ≠ 0 ∧ (∀ e, e ∉ F → y e = 0) ∧ ∀ C ∈ 𝒞, ∑ e ∈ C, y e = 0 := by
  let L : (S → ℝ) →ₗ[ℝ] ((𝒞 → ℝ) × ((Fᶜ : Finset S) → ℝ)) :=
    LinearMap.prod (LinearMap.pi fun C : 𝒞 => ∑ e ∈ C.1, LinearMap.proj e)
      (LinearMap.pi fun e : (Fᶜ : Finset S) => LinearMap.proj e.1)
  have hdim : Module.finrank ℝ ((𝒞 → ℝ) × ((Fᶜ : Finset S) → ℝ)) <
      Module.finrank ℝ (S → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_coe, Finset.card_compl]
    have := Finset.card_le_univ F
    omega
  obtain ⟨y, hyk, hy0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim)
  rw [LinearMap.mem_ker] at hyk
  refine ⟨y, hy0, fun e he => ?_, fun C hC => ?_⟩
  · have := congrArg (fun p => p.2 ⟨e, Finset.mem_compl.2 he⟩) hyk
    simpa [L] using this
  · have := congrArg (fun p => p.1 ⟨C, hC⟩) hyk
    simpa [L] using this

lemma exists_two_family (F : Finset S) (hF : F.Nonempty) (𝒬₁ 𝒬₂ : Finset (Finset S))
    (h₁ : 2 * 𝒬₁.card ≤ F.card) (h₂ : 2 * 𝒬₂.card ≤ F.card)
    (he₁ : 2 * 𝒬₁.card = F.card → ∀ y : S → ℝ, ∑ Q ∈ 𝒬₁, ∑ e ∈ Q, y e = ∑ e ∈ F, y e)
    (he₂ : 2 * 𝒬₂.card = F.card → ∀ y : S → ℝ, ∑ Q ∈ 𝒬₂, ∑ e ∈ Q, y e = ∑ e ∈ F, y e) :
    ∃ y : S → ℝ, y ≠ 0 ∧ (∀ e, e ∉ F → y e = 0) ∧ (∀ Q ∈ 𝒬₁, ∑ e ∈ Q, y e = 0) ∧
      ∀ Q ∈ 𝒬₂, ∑ e ∈ Q, y e = 0 := by
  have hFpos := hF.card_pos
  by_cases hlt : 𝒬₁.card + 𝒬₂.card < F.card
  · obtain ⟨y, hy0, hyF, hy⟩ := exists_kernel F (𝒬₁ ∪ 𝒬₂)
      (lt_of_le_of_lt (Finset.card_union_le _ _) hlt)
    exact ⟨y, hy0, hyF, fun Q hQ => hy Q (Finset.mem_union_left _ hQ),
      fun Q hQ => hy Q (Finset.mem_union_right _ hQ)⟩
  · have e1 : 2 * 𝒬₁.card = F.card := by omega
    have e2 : 2 * 𝒬₂.card = F.card := by omega
    obtain ⟨Q₀, hQ₀⟩ : 𝒬₂.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨y, hy0, hyF, hy⟩ := exists_kernel F (𝒬₁ ∪ 𝒬₂.erase Q₀) (by
      have := Finset.card_union_le 𝒬₁ (𝒬₂.erase Q₀)
      have := Finset.card_erase_of_mem hQ₀
      omega)
    have hA : ∀ Q ∈ 𝒬₁, ∑ e ∈ Q, y e = 0 := fun Q hQ => hy Q (Finset.mem_union_left _ hQ)
    have hB : ∀ Q ∈ 𝒬₂.erase Q₀, ∑ e ∈ Q, y e = 0 :=
      fun Q hQ => hy Q (Finset.mem_union_right _ hQ)
    refine ⟨y, hy0, hyF, hA, fun Q hQ => ?_⟩
    by_cases hQQ : Q = Q₀
    · subst hQQ
      have s1 := he₁ e1 y
      have s2 := he₂ e2 y
      rw [Finset.sum_eq_zero hA] at s1
      rw [← Finset.add_sum_erase _ _ hQ, Finset.sum_eq_zero hB, add_zero] at s2
      linarith
    · exact hB Q (Finset.mem_erase.2 ⟨hQQ, hQ⟩)

/-- `B` is tight for `M` at `x`. -/
def tight (M : FinMatroid S) (x : S → ℝ) (B : Finset S) : Prop :=
  ∑ e ∈ B, x e = (rank M B : ℝ)

/-- `e` and `f` lie in the same tight sets. -/
def sameT (M : FinMatroid S) (x : S → ℝ) (e f : S) : Prop :=
  ∀ B, tight M x B → (e ∈ B ↔ f ∈ B)

open Classical in
noncomputable def cls (M : FinMatroid S) (x : S → ℝ) (F : Finset S) (e : S) : Finset S :=
  F.filter (fun f => sameT M x e f)

open Classical in
lemma mem_cls (M : FinMatroid S) (x : S → ℝ) (F : Finset S) (e f : S) :
    f ∈ cls M x F e ↔ f ∈ F ∧ sameT M x e f := by
  unfold cls; exact Finset.mem_filter

lemma tight_empty (M : FinMatroid S) (x : S → ℝ) : tight M x ∅ := by
  unfold tight
  have := rank_le_card M ∅
  rw [Finset.card_empty, Nat.le_zero] at this
  simp [this]

lemma tight_inter_union (M : FinMatroid S) {x : S → ℝ}
    (hx : ∀ A, ∑ e ∈ A, x e ≤ (rank M A : ℝ)) {B C : Finset S}
    (hB : tight M x B) (hC : tight M x C) : tight M x (B ∩ C) ∧ tight M x (B ∪ C) := by
  unfold tight at *
  have h1 := Finset.sum_union_inter (s₁ := B) (s₂ := C) (f := x)
  have h2 : ((rank M (B ∩ C) : ℕ) : ℝ) + rank M (B ∪ C) ≤ rank M B + rank M C := by
    exact_mod_cast rank_submod M B C
  have h3 := hx (B ∩ C)
  have h4 := hx (B ∪ C)
  constructor <;> linarith

lemma class_eq (M : FinMatroid S) {x : S → ℝ} (hx : ∀ A, ∑ e ∈ A, x e ≤ (rank M A : ℝ))
    (e : S) (hB : ∃ B, tight M x B ∧ e ∈ B) :
    ∃ m L : Finset S, tight M x m ∧ tight M x L ∧ L ⊆ m ∧
      ∀ f, sameT M x e f ↔ (f ∈ m ∧ f ∉ L) := by
  classical
  obtain ⟨m, hm, hmin⟩ := (Finset.univ.filter (fun B => tight M x B ∧ e ∈ B)).exists_min_image
    Finset.card (by obtain ⟨B, h⟩ := hB; exact ⟨B, by simp [h]⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm hmin
  have hmsub : ∀ C, tight M x C → e ∈ C → m ⊆ C := by
    intro C hC heC
    have hi := (tight_inter_union M hx hC hm.1).1
    have := hmin (C ∩ m) ⟨hi, Finset.mem_inter.2 ⟨heC, hm.2⟩⟩
    have heq : C ∩ m = m := Finset.eq_of_subset_of_card_le Finset.inter_subset_right this
    rw [← heq]; exact Finset.inter_subset_left
  obtain ⟨L, hL, hmax⟩ := (Finset.univ.filter
    (fun B => tight M x B ∧ B ⊆ m ∧ e ∉ B)).exists_max_image Finset.card
      ⟨∅, by simp [tight_empty M x]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL hmax
  have hLsub : ∀ C, tight M x C → C ⊆ m → e ∉ C → C ⊆ L := by
    intro C hC hCm heC
    have hu := (tight_inter_union M hx hC hL.1).2
    have := hmax (C ∪ L) ⟨hu, Finset.union_subset hCm hL.2.1, by simp [heC, hL.2.2]⟩
    have heq : C ∪ L = L :=
      (Finset.eq_of_subset_of_card_le Finset.subset_union_right this).symm
    rw [← heq]; exact Finset.subset_union_left
  refine ⟨m, L, hm.1, hL.1, hL.2.1, fun f => ⟨fun h => ⟨(h m hm.1).1 hm.2,
    fun hfL => hL.2.2 ((h L hL.1).2 hfL)⟩, fun ⟨hfm, hfL⟩ B hB => ⟨fun heB => hmsub B hB heB hfm,
    fun hfB => ?_⟩⟩⟩
  by_contra heB
  have hi := (tight_inter_union M hx hB hm.1).1
  exact hfL (hLsub _ hi Finset.inter_subset_right (fun h => heB (Finset.mem_inter.1 h).1)
    (Finset.mem_inter.2 ⟨hfB, hfm⟩))

lemma sum_01_nat {x : S → ℝ} (D : Finset S) :
    (∀ e ∈ D, x e = 0 ∨ x e = 1) → ∃ n : ℕ, ∑ e ∈ D, x e = n := by
  refine Finset.induction_on D ?_ ?_
  · intro _; exact ⟨0, by simp⟩
  · intro a D ha ih h
    obtain ⟨n, hn⟩ := ih (fun e he => h e (Finset.mem_insert_of_mem he))
    rw [Finset.sum_insert ha, hn]
    rcases h a (Finset.mem_insert_self a D) with h0 | h1
    · exact ⟨n, by rw [h0, zero_add]⟩
    · exact ⟨n + 1, by rw [h1]; push_cast; ring⟩

lemma family (M : FinMatroid S) {x : S → ℝ} (hx : ∀ A, ∑ e ∈ A, x e ≤ (rank M A : ℝ))
    (F : Finset S) (hF : ∀ e, e ∈ F ↔ (0 < x e ∧ x e < 1))
    (h01 : ∀ e, e ∉ F → x e = 0 ∨ x e = 1) :
    ∃ 𝒬 : Finset (Finset S), 2 * 𝒬.card ≤ F.card ∧
      (2 * 𝒬.card = F.card → ∀ y : S → ℝ, ∑ Q ∈ 𝒬, ∑ e ∈ Q, y e = ∑ e ∈ F, y e) ∧
      ∀ y : S → ℝ, (∀ e, e ∉ F → y e = 0) → (∀ Q ∈ 𝒬, ∑ e ∈ Q, y e = 0) →
        ∀ B, tight M x B → ∑ e ∈ B, y e = 0 := by
  classical
  set K := cls M x F with hKdef
  set Fj := F.filter (fun e => ∃ B, tight M x B ∧ e ∈ B) with hFj
  have hKK : ∀ e f, sameT M x e f → K f = K e := by
    intro e f hef; ext g; rw [hKdef, mem_cls, mem_cls]; constructor
    · rintro ⟨hg, hfg⟩; exact ⟨hg, fun B hB => (hef B hB).trans (hfg B hB)⟩
    · rintro ⟨hg, heg⟩; exact ⟨hg, fun B hB => (hef B hB).symm.trans (heg B hB)⟩
  have hmemK : ∀ e ∈ F, e ∈ K e := fun e he => (mem_cls M x F e e).2 ⟨he, fun B _ => Iff.rfl⟩
  have hfib : ∀ s : Finset S, s ⊆ F → (∀ e ∈ s, ∀ f ∈ K e, f ∈ s) → ∀ e ∈ s,
      s.filter (fun f => K f = K e) = K e := by
    intro s hsF hs e he
    ext f; rw [Finset.mem_filter]; constructor
    · rintro ⟨hfs, hfe⟩; rw [← hfe]; exact hmemK f (hsF hfs)
    · intro hf; exact ⟨hs e he f hf, hKK e f ((mem_cls M x F e f).1 hf).2⟩
  have hFjc : ∀ e ∈ Fj, ∀ f ∈ K e, f ∈ Fj := by
    intro e he f hf
    rw [hFj, Finset.mem_filter] at he ⊢
    obtain ⟨hfF, hsame⟩ := (mem_cls M x F e f).1 hf
    obtain ⟨B, hB, heB⟩ := he.2
    exact ⟨hfF, B, hB, (hsame B hB).1 heB⟩
  have hcard2 : ∀ e ∈ Fj, 2 ≤ (K e).card := by
    intro e he
    rw [hFj, Finset.mem_filter] at he
    obtain ⟨m, L, hm, hL, hLm, hiff⟩ := class_eq M hx e he.2
    have hKeq : K e = (m \ L).filter (· ∈ F) := by
      ext f; rw [hKdef, mem_cls, Finset.mem_filter, Finset.mem_sdiff, hiff f]; tauto
    have hsplit := Finset.sum_filter_add_sum_filter_not (m \ L) (· ∈ F) x
    rw [Finset.sum_sdiff_eq_sub hLm, hm, hL, ← hKeq] at hsplit
    obtain ⟨n, hn⟩ := sum_01_nat ((m \ L).filter (fun f => ¬ f ∈ F)) (fun f hf =>
      h01 f (Finset.mem_filter.1 hf).2)
    by_contra hlt0
    have hlt : (K e).card ≤ 1 := by omega
    have hsing : K e = {e} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hmemK e he.1, fun f hf => ?_⟩
      exact Finset.card_le_one.1 (by omega) f hf e (hmemK e he.1)
    rw [hsing, Finset.sum_singleton, hn] at hsplit
    have hxe := (hF e).1 he.1
    have hz : x e = (((rank M m : ℤ) - rank M L - n : ℤ) : ℝ) := by push_cast; linarith
    rw [hz] at hxe
    have a1 : (0 : ℤ) < (rank M m : ℤ) - rank M L - n := by exact_mod_cast hxe.1
    have a2 : (rank M m : ℤ) - rank M L - n < 1 := by exact_mod_cast hxe.2
    omega
  refine ⟨Fj.image K, ?_, ?_, ?_⟩
  · have hc := Finset.card_eq_sum_card_image K Fj
    have hle : ∑ Q ∈ Fj.image K, 2 ≤ ∑ Q ∈ Fj.image K, (Fj.filter (fun f => K f = Q)).card := by
      refine Finset.sum_le_sum fun Q hQ => ?_
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hQ
      rw [hfib Fj (Finset.filter_subset _ _) hFjc e he]
      exact hcard2 e he
    rw [Finset.sum_const, smul_eq_mul] at hle
    have := Finset.card_le_card (Finset.filter_subset (fun e => ∃ B, tight M x B ∧ e ∈ B) F)
    rw [← hFj] at this
    omega
  · intro heq y
    have hc := Finset.card_eq_sum_card_image K Fj
    have hle : ∑ Q ∈ Fj.image K, 2 ≤ ∑ Q ∈ Fj.image K, (Fj.filter (fun f => K f = Q)).card := by
      refine Finset.sum_le_sum fun Q hQ => ?_
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hQ
      rw [hfib Fj (Finset.filter_subset _ _) hFjc e he]
      exact hcard2 e he
    rw [Finset.sum_const, smul_eq_mul] at hle
    have hsub : Fj ⊆ F := Finset.filter_subset _ _
    have hFjF : Fj = F := Finset.eq_of_subset_of_card_le hsub (by omega)
    calc ∑ Q ∈ Fj.image K, ∑ e ∈ Q, y e
        = ∑ Q ∈ Fj.image K, ∑ e ∈ Fj with K e = Q, y e := by
          refine Finset.sum_congr rfl fun Q hQ => ?_
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hQ
          rw [hfib Fj hsub hFjc e he]
      _ = ∑ e ∈ Fj, y e := Finset.sum_fiberwise_of_maps_to
          (fun e he => Finset.mem_image_of_mem K he) y
      _ = ∑ e ∈ F, y e := by rw [hFjF]
  · intro y hyF hyQ B hB
    set s := B.filter (· ∈ F) with hs
    have h1 : ∑ e ∈ B, y e = ∑ e ∈ s, y e := by
      rw [hs, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs with h
      · rfl
      · exact hyF e h
    have hsF : s ⊆ F := fun e he => (Finset.mem_filter.1 he).2
    have hsc : ∀ e ∈ s, ∀ f ∈ K e, f ∈ s := by
      intro e he f hf
      obtain ⟨heB, _⟩ := Finset.mem_filter.1 he
      obtain ⟨hfF, hsame⟩ := (mem_cls M x F e f).1 hf
      exact Finset.mem_filter.2 ⟨(hsame B hB).1 heB, hfF⟩
    rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image K) (g := K)
      (fun e he => Finset.mem_image_of_mem K he) y]
    refine Finset.sum_eq_zero fun Q hQ => ?_
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hQ
    rw [hfib s hsF hsc e he]
    refine hyQ _ (Finset.mem_image.2 ⟨e, ?_, rfl⟩)
    obtain ⟨heB, heF⟩ := Finset.mem_filter.1 he
    rw [hFj, Finset.mem_filter]
    exact ⟨heF, B, hB, heB⟩

lemma extreme_sub (M₁ M₂ : FinMatroid S) : (intersectionLP M₁ M₂).extremePoints ℝ ⊆
    {x : S → ℝ | ∃ J : Finset S, M₁.Indep J ∧ M₂.Indep J ∧ x = charVec J} := by
  classical
  intro x hext
  have hx := extremePoints_subset hext
  have hx' := hx
  simp only [intersectionLP, Set.mem_ofPred_eq] at hx'
  by_cases hfrac : ∃ e, 0 < x e ∧ x e < 1
  · exfalso
    set F := Finset.univ.filter (fun e => 0 < x e ∧ x e < 1) with hFdef
    have hF : ∀ e, e ∈ F ↔ (0 < x e ∧ x e < 1) := by intro e; simp [hFdef]
    have h01 : ∀ e, e ∉ F → x e = 0 ∨ x e = 1 := by
      intro e he
      rw [hF] at he
      have h0 := hx'.2.2 e
      have h1 := le_one_of_mem M₁ M₂ hx e
      rcases h0.lt_or_eq with h | h
      · right; by_contra hc; exact he ⟨h, lt_of_le_of_ne h1 hc⟩
      · left; exact h.symm
    obtain ⟨𝒬₁, a1, b1, c1⟩ := family M₁ hx'.1 F hF h01
    obtain ⟨𝒬₂, a2, b2, c2⟩ := family M₂ hx'.2.1 F hF h01
    have hFne : F.Nonempty := by obtain ⟨e, he⟩ := hfrac; exact ⟨e, (hF e).2 he⟩
    obtain ⟨y, hy0, hyF, hy1, hy2⟩ := exists_two_family F hFne 𝒬₁ 𝒬₂ a1 a2 b1 b2
    exact not_extreme_of_dir M₁ M₂ hx hy0
      (fun e he => hyF e (fun hm => by rw [hF] at hm; linarith [hm.1]))
      (fun A hA => c1 y hyF hy1 A hA) (fun A hA => c2 y hyF hy2 A hA) hext
  · have hfrac : ∀ e, 0 < x e → 1 ≤ x e := fun e h => not_lt.1 (fun h' => hfrac ⟨e, h, h'⟩)
    refine ext_of_01 M₁ M₂ hx (fun e => ?_)
    have h0 := hx'.2.2 e
    have h1 := le_one_of_mem M₁ M₂ hx e
    rcases h0.lt_or_eq with h | h
    · right; exact le_antisymm h1 (hfrac e h)
    · left; exact h.symm

end MIPAux

open CombOpt.MatroidIntersectionPolytope in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : FinMatroid S) :
    convexHull ℝ {x : S → ℝ | ∃ J : Finset S, M₁.Indep J ∧ M₂.Indep J ∧ x = CombOpt.TJoin.charVec J} =
      intersectionLP M₁ M₂ := by
  exact MIPAux.glue M₁ M₂ (MIPAux.extreme_sub M₁ M₂)
