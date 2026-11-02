-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.lovasz_extension_is_zero_l
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:50:30.345881+00:00
-- url     : https://prove2.me/submissions/1eea2d65-86c5-435b-85cd-452280cc7f36

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValued
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LovaszExtension
import Theorems.Thm_DiscreteConvex_MConvexSetsB_lovasz_convex_iff_submodular

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsD

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

variable {V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def lovaszList (rho : Finset V → WithTop ℝ) (p : V → ℝ) : List ℝ → WithTop ℝ
  | [] => 0
  | [a] => PosScalarMul a (rho (Finset.univ.filter (fun v => a ≤ p v)))
  | a :: b :: rest =>
      PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ p v))) +
        lovaszList rho p (b :: rest)

private lemma posScalarMul_zero (x : WithTop ℝ) : PosScalarMul 0 x = 0 := by
  cases x <;> simp [PosScalarMul]

private lemma posScalarMul_one (x : WithTop ℝ) : PosScalarMul 1 x = x := by
  cases x <;> simp [PosScalarMul]

private lemma posScalarMul_add_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : WithTop ℝ) :
    PosScalarMul (a + b) x = PosScalarMul a x + PosScalarMul b x := by
  cases x with
  | top =>
    have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hb0 : b ≠ 0 := ne_of_gt hb
    simp [PosScalarMul, hab, ha0, hb0]
  | coe r =>
    dsimp [PosScalarMul]
    exact_mod_cast add_mul a b r

private lemma posScalarMul_distrib_add {t : ℝ} (ht : 0 < t) (x y : WithTop ℝ) :
    PosScalarMul t (x + y) = PosScalarMul t x + PosScalarMul t y := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  cases x with
  | top => simp [PosScalarMul, ht0]
  | coe rx =>
    cases y with
    | top => simp [PosScalarMul, ht0]
    | coe ry =>
      change (((t * (rx + ry) : ℝ) : WithTop ℝ)) = (((t * rx : ℝ) : WithTop ℝ)) + (((t * ry : ℝ) : WithTop ℝ))
      rw [← WithTop.coe_add]
      exact_mod_cast mul_add t rx ry

private lemma posScalarMul_mul_pos {t a : ℝ} (ht : 0 < t) (x : WithTop ℝ) :
    PosScalarMul (t * a) x = PosScalarMul t (PosScalarMul a x) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  cases x with
  | top =>
    by_cases ha : a = 0
    · subst ha; simp [PosScalarMul]
    · have hta : t * a ≠ 0 := mul_ne_zero ht0 ha
      simp [PosScalarMul, ht0, ha, hta]
  | coe r =>
    dsimp [PosScalarMul]
    exact_mod_cast mul_assoc t a r

private lemma posScalarMul_sub_add_coe {a c r : ℝ} :
    PosScalarMul (a - c) (r : WithTop ℝ) + PosScalarMul c (r : WithTop ℝ) =
      PosScalarMul a (r : WithTop ℝ) := by
  dsimp [PosScalarMul]
  exact_mod_cast (by ring : (a - c) * r + c * r = a * r)

private lemma posScalarMul_le_add_of_nonneg {c : ℝ} (hc : 0 ≤ c) {x y z w : WithTop ℝ}
    (h : z + w ≤ x + y) :
    PosScalarMul c z + PosScalarMul c w ≤ PosScalarMul c x + PosScalarMul c y := by
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · simp [posScalarMul_zero]
  · by_cases hx : x = ⊤
    · subst hx
      simp [PosScalarMul, ne_of_gt hc_pos]
    · by_cases hy : y = ⊤
      · subst hy
        simp [PosScalarMul, ne_of_gt hc_pos]
      · lift x to ℝ using hx
        lift y to ℝ using hy
        have hzw_ne : z + w ≠ ⊤ := by
          intro htop
          rw [htop] at h
          exact WithTop.coe_ne_top (top_le_iff.mp (h.trans_eq (WithTop.coe_add x y).symm))
        have hz : z ≠ ⊤ := fun htop => hzw_ne (by simp [htop])
        have hw : w ≠ ⊤ := fun htop => hzw_ne (by simp [htop])
        lift z to ℝ using hz
        lift w to ℝ using hw
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
        dsimp [PosScalarMul]
        exact_mod_cast (by nlinarith : c * z + c * w ≤ c * x + c * y)

private lemma lovaszList_eq_sum (rho : Finset V → WithTop ℝ) (p : V → ℝ) :
    ∀ (L : List ℝ),
      lovaszList rho p L =
        (∑ i ∈ Finset.range (L.length - 1),
            PosScalarMul (L.getD i 0 - L.getD (i + 1) 0)
              (rho (Finset.univ.filter (fun v => L.getD i 0 ≤ p v)))) +
          PosScalarMul (L.getD (L.length - 1) 0)
            (rho (Finset.univ.filter (fun v => L.getD (L.length - 1) 0 ≤ p v)))
  | [] => by simp [lovaszList, posScalarMul_zero]
  | [a] => by simp [lovaszList]
  | a :: b :: rest => by
      have ih := lovaszList_eq_sum rho p (b :: rest)
      simp only [lovaszList, ih, List.length_cons, Nat.add_sub_cancel]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      ac_rfl

private lemma lovaszList_sortedValues (rho : Finset V → WithTop ℝ) (p : V → ℝ) :
    lovaszList rho p (SortedValues p) = LovaszExtension rho p := by
  unfold LovaszExtension ThresholdSet
  rw [lovaszList_eq_sum]
  by_cases hlen : (SortedValues p).length = 0
  · simp [hlen]
  · simp

private noncomputable def insLow (c : ℝ) : List ℝ → List ℝ
  | [] => [c]
  | a :: rest => if c = a then a :: rest else if a < c then c :: a :: rest else a :: insLow c rest

private lemma mem_insLow {c x : ℝ} : ∀ {L : List ℝ}, x ∈ insLow c L ↔ x = c ∨ x ∈ L
  | [] => by simp [insLow]
  | a :: rest => by
      simp only [insLow]
      split_ifs with h1 h2
      · subst h1; simp
      · simp
      · simp [mem_insLow]; tauto

private lemma insLow_ne_nil (c : ℝ) : ∀ (L : List ℝ), insLow c L ≠ []
  | [] => by simp [insLow]
  | a :: rest => by
      simp only [insLow]
      split_ifs <;> simp

private lemma pairwise_insLow (c : ℝ) :
    ∀ {L : List ℝ}, List.Pairwise (· > ·) L → List.Pairwise (· > ·) (insLow c L)
  | [], _ => List.pairwise_singleton _ _
  | a :: rest, hpw => by
      rcases List.pairwise_cons.mp hpw with ⟨ha, hrest⟩
      simp only [insLow]
      split_ifs with h1 h2
      · exact hpw
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, hpw⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h2
        · exact lt_trans (ha x hx') h2
      · have hac : c < a := lt_of_le_of_ne (not_lt.mp h2) h1
        rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, pairwise_insLow c hrest⟩
        rcases mem_insLow.mp hx with rfl | hx'
        · exact hac
        · exact ha x hx'

private lemma pairwise_gt_sort (s : Finset ℝ) : List.Pairwise (· > ·) (s.sort (· ≥ ·)) := by
  have hle := Finset.pairwise_sort s (· ≥ ·)
  have hnd := Finset.sort_nodup s (· ≥ ·)
  rw [List.Nodup, List.pairwise_iff_getElem] at hnd
  rw [List.pairwise_iff_getElem] at hle ⊢
  intro i j hi hj hij
  exact lt_of_le_of_ne (hle i j hi hj hij) (Ne.symm (hnd i j hi hj hij))

private lemma eq_of_pairwise_gt :
    ∀ {L₁ L₂ : List ℝ}, List.Pairwise (· > ·) L₁ → List.Pairwise (· > ·) L₂ →
      (∀ x, x ∈ L₁ ↔ x ∈ L₂) → L₁ = L₂
  | [], [], _, _, _ => rfl
  | a :: L₁, [], _, _, hiff => False.elim ((List.not_mem_nil) ((hiff a).mp List.mem_cons_self))
  | [], b :: L₂, _, _, hiff => False.elim ((List.not_mem_nil) ((hiff b).mpr List.mem_cons_self))
  | a :: L₁, b :: L₂, hpw₁, hpw₂, hiff => by
      rcases List.pairwise_cons.mp hpw₁ with ⟨ha, hrest₁⟩
      rcases List.pairwise_cons.mp hpw₂ with ⟨hb, hrest₂⟩
      have hab : a = b := by
        have ha_mem : a ∈ b :: L₂ := (hiff a).mp List.mem_cons_self
        have hb_mem : b ∈ a :: L₁ := (hiff b).mpr List.mem_cons_self
        rcases List.mem_cons.mp ha_mem with rfl | ha'
        · rfl
        · rcases List.mem_cons.mp hb_mem with rfl | hb'
          · rfl
          · exact False.elim (lt_asymm (hb a ha') (ha b hb'))
      subst hab
      congr 1
      refine eq_of_pairwise_gt hrest₁ hrest₂ (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
      · have hx' : x ∈ a :: L₂ := (hiff x).mp (List.mem_cons_of_mem a hx)
        rcases List.mem_cons.mp hx' with rfl | hx₂
        · exact False.elim (lt_irrefl x (ha x hx))
        · exact hx₂
      · have hx' : x ∈ a :: L₁ := (hiff x).mpr (List.mem_cons_of_mem a hx)
        rcases List.mem_cons.mp hx' with rfl | hx₁
        · exact False.elim (lt_irrefl x (hb x hx))
        · exact hx₁

private lemma lovaszList_insLow_lt (rho : Finset V → WithTop ℝ)
    (hrhoV : rho Finset.univ ≠ ⊤) (p : V → ℝ) (c : ℝ) :
    ∀ (L : List ℝ) (_ : L ≠ []),
      List.Pairwise (· > ·) L →
      (∀ v : V, p v ∈ L ∨ ∀ x ∈ L, x < p v) →
      (∀ a ∈ L.head?, c < a) →
      lovaszList rho p (insLow c L) = lovaszList rho p L
  | [], hL, _, _, _ => False.elim (hL rfl)
  | [a], _, hpw, hcov, hlt => by
      have hca : c < a := hlt a rfl
      have hne : c ≠ a := ne_of_lt hca
      have hnot : ¬ a < c := not_lt_of_gt hca
      simp only [insLow, hne, hnot, ite_false]
      have hfa : Finset.univ.filter (fun v => a ≤ p v) = Finset.univ := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        rcases hcov v with hv | hv
        · simp only [List.mem_singleton] at hv; linarith
        · exact le_of_lt (hv a (List.mem_singleton.mpr rfl))
      have hfc : Finset.univ.filter (fun v => c ≤ p v) = Finset.univ := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have : a ≤ p v := by
          have : v ∈ Finset.univ.filter (fun v => a ≤ p v) := by rw [hfa]; exact Finset.mem_univ v
          exact (Finset.mem_filter.mp this).2
        linarith
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hrhoV
      simp only [lovaszList, hfa, hfc, ← hr]
      exact posScalarMul_sub_add_coe
  | a :: b :: rest, _, hpw, hcov, hlt => by
      have hca : c < a := hlt a rfl
      have hne : c ≠ a := ne_of_lt hca
      have hnot : ¬ a < c := not_lt_of_gt hca
      rcases List.pairwise_cons.mp hpw with ⟨ha_gt, hpw'⟩
      have hab : a > b := ha_gt b List.mem_cons_self
      have hcov' : ∀ v : V, p v ∈ b :: rest ∨ ∀ x ∈ b :: rest, x < p v := by
        intro v
        rcases hcov v with hv | hv
        · rcases List.mem_cons.mp hv with hva | hva'
          · right
            intro x hx
            rw [hva]
            exact ha_gt x hx
          · left; exact hva'
        · right
          intro x hx
          exact hv x (List.mem_cons_of_mem a hx)
      by_cases hcb : c = b
      · subst hcb
        simp [insLow, hne, hnot]
      · by_cases hbc : b < c
        · simp only [insLow, hne, hnot, hcb, hbc, ite_true, ite_false, lovaszList]
          have hfc_eq_fa : Finset.univ.filter (fun v => c ≤ p v) =
              Finset.univ.filter (fun v => a ≤ p v) := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨fun hcp => ?_, fun hap => le_trans (le_of_lt hca) hap⟩
            rcases hcov v with hv | hv
            · rcases List.mem_cons.mp hv with hva | hva'
              · linarith
              · rcases List.mem_cons.mp hva' with hvb | hvrest
                · linarith
                · have hbx : b > p v := (List.pairwise_cons.mp hpw').1 (p v) hvrest
                  linarith
            · exact le_of_lt (hv a List.mem_cons_self)
          rw [hfc_eq_fa, ← add_assoc]
          congr 1
          have h1 : 0 < a - c := sub_pos.mpr hca
          have h2 : 0 < c - b := sub_pos.mpr hbc
          have hsum : (a - c) + (c - b) = a - b := by ring
          rw [← posScalarMul_add_of_pos h1 h2, hsum]
        · have hcb' : c < b := lt_of_le_of_ne (not_lt.mp hbc) hcb
          have ih := lovaszList_insLow_lt rho hrhoV p c (b :: rest) (by simp) hpw' hcov'
            (by intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; subst hx; exact hcb')
          have h_ins_b : insLow c (b :: rest) = b :: insLow c rest := by
            simp [insLow, hcb, hbc]
          have h_ins_a : insLow c (a :: b :: rest) = a :: b :: insLow c rest := by
            simp [insLow, hne, hnot, hcb, hbc]
          rw [h_ins_b] at ih
          rw [h_ins_a]
          simp only [lovaszList, ih]

private lemma lovaszList_insLow (rho : Finset V → WithTop ℝ) (hrho : SubmodularSetFunction rho)
    (p : V → ℝ) (c : ℝ) (L : List ℝ) (hL : L ≠ [])
    (hpw : List.Pairwise (· > ·) L) (hmem : ∀ v : V, p v ∈ L) :
    lovaszList rho p (insLow c L) = lovaszList rho p L := by
  cases L with
  | nil => exact False.elim (hL rfl)
  | cons a rest =>
    by_cases hca : c = a
    · subst hca; simp [insLow]
    · by_cases hac : a < c
      · have h_ins : insLow c (a :: rest) = c :: a :: rest := by simp [insLow, hca, hac]
        rw [h_ins]
        have hfc_empty : Finset.univ.filter (fun v => c ≤ p v) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro v _
          rw [not_le]
          have hv : p v ∈ a :: rest := hmem v
          rcases List.mem_cons.mp hv with hva | hvrest
          · linarith
          · have hap : a > p v := (List.pairwise_cons.mp hpw).1 (p v) hvrest
            linarith
        simp only [lovaszList, hfc_empty, hrho.1]
        have h0 : PosScalarMul (c - a) 0 = 0 := by simp [PosScalarMul]
        rw [h0, zero_add]
      · have hca' : c < a := lt_of_le_of_ne (not_lt.mp hac) hca
        exact lovaszList_insLow_lt rho hrho.2.1 p c (a :: rest) (by simp) hpw
          (fun v => Or.inl (hmem v))
          (by intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; subst hx; exact hca')

private lemma lovaszList_foldr_insLow (rho : Finset V → WithTop ℝ) (hrho : SubmodularSetFunction rho)
    (p : V → ℝ) :
    ∀ (U : List ℝ) (L : List ℝ),
      L ≠ [] → List.Pairwise (· > ·) L → (∀ v : V, p v ∈ L) →
      lovaszList rho p (U.foldr insLow L) = lovaszList rho p L ∧
      U.foldr insLow L ≠ [] ∧
      List.Pairwise (· > ·) (U.foldr insLow L) ∧
      (∀ x, x ∈ U.foldr insLow L ↔ x ∈ U ∨ x ∈ L)
  | [], L, hL, hpw, hmem => ⟨rfl, hL, hpw, fun x => by simp⟩
  | c :: U, L, hL, hpw, hmem => by
      rcases lovaszList_foldr_insLow rho hrho p U L hL hpw hmem with ⟨heq, hne', hpw', hmem'⟩
      have hmem_p : ∀ v : V, p v ∈ U.foldr insLow L := fun v => (hmem' (p v)).mpr (Or.inr (hmem v))
      refine ⟨?_, insLow_ne_nil c _, pairwise_insLow c hpw', fun x => ?_⟩
      · simp only [List.foldr_cons]
        rw [lovaszList_insLow rho hrho p c (U.foldr insLow L) hne' hpw' hmem_p, heq]
      · simp only [List.foldr_cons, mem_insLow, hmem', List.mem_cons]
        tauto

private lemma sortedValues_ne_nil [Nonempty V] (p : V → ℝ) : SortedValues p ≠ [] := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  intro h
  have hv₀ : p v₀ ∈ SortedValues p := by
    unfold SortedValues
    rw [Finset.mem_sort]
    exact Finset.mem_image_of_mem p (Finset.mem_univ v₀)
  rw [h] at hv₀
  exact List.not_mem_nil hv₀

private lemma mem_sortedValues (p : V → ℝ) (v : V) : p v ∈ SortedValues p := by
  unfold SortedValues
  rw [Finset.mem_sort]
  exact Finset.mem_image_of_mem p (Finset.mem_univ v)

private lemma pairwise_sortedValues (p : V → ℝ) : List.Pairwise (· > ·) (SortedValues p) :=
  pairwise_gt_sort _

private lemma lovasz_eq_lovaszList_of_mem [Nonempty V] (rho : Finset V → WithTop ℝ)
    (hrho : SubmodularSetFunction rho) (p : V → ℝ) (L : List ℝ)
    (hpw : List.Pairwise (· > ·) L) (hmem : ∀ v : V, p v ∈ L) :
    LovaszExtension rho p = lovaszList rho p L := by
  rcases lovaszList_foldr_insLow rho hrho p L (SortedValues p)
    (sortedValues_ne_nil p) (pairwise_sortedValues p) (mem_sortedValues p) with
    ⟨heq, _, hpw_fold, hmem_fold⟩
  have hL_eq : L.foldr insLow (SortedValues p) = L := by
    refine eq_of_pairwise_gt hpw_fold hpw (fun x => ?_)
    rw [hmem_fold]
    refine ⟨fun hx => ?_, fun hx => Or.inl hx⟩
    rcases hx with hx | hx
    · exact hx
    · have hx' := (Finset.mem_sort (· ≥ ·)).mp hx
      rcases Finset.mem_image.mp hx' with ⟨v, _, rfl⟩
      exact hmem v
  rw [← lovaszList_sortedValues, ← heq, hL_eq]

private lemma step_exists_le {p : V → ℝ} {a b : ℝ} {rest : List ℝ} (hab : a > b)
    (hp : ∀ v : V, ∃ x ∈ a :: b :: rest, x ≤ p v) :
    ∀ v : V, ∃ x ∈ b :: rest, x ≤ p v := by
  intro v
  rcases hp v with ⟨x, hx, hxp⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact ⟨b, List.mem_cons_self, le_trans (le_of_lt hab) hxp⟩
  · exact ⟨x, hx', hxp⟩

private lemma lovaszList_sbfr (rho : Finset V → WithTop ℝ) (hrho : SubmodularSetFunction rho)
    (p q : V → ℝ) :
    ∀ (L : List ℝ), List.Pairwise (· > ·) L →
      (∀ v : V, ∃ x ∈ L, x ≤ p v) →
      (∀ v : V, ∃ x ∈ L, x ≤ q v) →
      lovaszList rho (p ⊔ q) L + lovaszList rho (p ⊓ q) L ≤
        lovaszList rho p L + lovaszList rho q L
  | [], _, _, _ => by simp [lovaszList]
  | [a], _, hp, hq => by
      have hap : ∀ v : V, a ≤ p v := by
        intro v; rcases hp v with ⟨x, hx, hxp⟩; simp only [List.mem_singleton] at hx; linarith
      have haq : ∀ v : V, a ≤ q v := by
        intro v; rcases hq v with ⟨x, hx, hxq⟩; simp only [List.mem_singleton] at hx; linarith
      have hfp : Finset.univ.filter (fun v => a ≤ p v) = Finset.univ := by
        ext v; simp [hap v]
      have hfq : Finset.univ.filter (fun v => a ≤ q v) = Finset.univ := by
        ext v; simp [haq v]
      have hfsup : Finset.univ.filter (fun v => a ≤ (p ⊔ q) v) = Finset.univ := by
        ext v; simp [Pi.sup_apply, le_sup_iff, hap v]
      have hfinf : Finset.univ.filter (fun v => a ≤ (p ⊓ q) v) = Finset.univ := by
        ext v; simp [Pi.inf_apply, le_inf_iff, hap v, haq v]
      simp only [lovaszList, hfp, hfq, hfsup, hfinf, le_rfl]
  | a :: b :: rest, hpw, hp, hq => by
      rcases List.pairwise_cons.mp hpw with ⟨ha_gt, hpw'⟩
      have hab : a > b := ha_gt b List.mem_cons_self
      have hab_nonneg : 0 ≤ a - b := sub_nonneg.mpr (le_of_lt hab)
      have h_union : Finset.univ.filter (fun v => a ≤ (p ⊔ q) v) =
          Finset.univ.filter (fun v => a ≤ p v) ∪ Finset.univ.filter (fun v => a ≤ q v) := by
        ext v; simp [Pi.sup_apply, le_sup_iff]
      have h_inter : Finset.univ.filter (fun v => a ≤ (p ⊓ q) v) =
          Finset.univ.filter (fun v => a ≤ p v) ∩ Finset.univ.filter (fun v => a ≤ q v) := by
        ext v; simp [Pi.inf_apply, le_inf_iff]
      have hhead := posScalarMul_le_add_of_nonneg hab_nonneg
        (hrho.2.2 (Finset.univ.filter (fun v => a ≤ p v)) (Finset.univ.filter (fun v => a ≤ q v)))
      have htail := lovaszList_sbfr rho hrho p q (b :: rest) hpw'
        (step_exists_le hab hp) (step_exists_le hab hq)
      simp only [lovaszList, h_union, h_inter]
      calc
        (PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ p v) ∪ Finset.univ.filter (fun v => a ≤ q v))) +
          lovaszList rho (p ⊔ q) (b :: rest)) +
        (PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ p v) ∩ Finset.univ.filter (fun v => a ≤ q v))) +
          lovaszList rho (p ⊓ q) (b :: rest))
        = (PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ p v) ∪ Finset.univ.filter (fun v => a ≤ q v))) +
            PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ p v) ∩ Finset.univ.filter (fun v => a ≤ q v)))) +
          (lovaszList rho (p ⊔ q) (b :: rest) + lovaszList rho (p ⊓ q) (b :: rest)) := by ac_rfl
        _ ≤ (PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ p v))) +
              PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ q v)))) +
            (lovaszList rho p (b :: rest) + lovaszList rho q (b :: rest)) := add_le_add hhead htail
        _ = (PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ p v))) +
              lovaszList rho p (b :: rest)) +
            (PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ q v))) +
              lovaszList rho q (b :: rest)) := by ac_rfl

private lemma lovaszList_map_add (rho : Finset V → WithTop ℝ) (r : ℝ)
    (hr : rho Finset.univ = (r : WithTop ℝ)) (p : V → ℝ) (alpha : ℝ) :
    ∀ (L : List ℝ), L ≠ [] → List.Pairwise (· > ·) L →
      (∀ v : V, ∃ x ∈ L, x ≤ p v) →
      lovaszList rho (fun v => p v + alpha) (L.map (· + alpha)) =
        lovaszList rho p L + ((alpha * r : ℝ) : WithTop ℝ)
  | [], hL, _, _ => False.elim (hL rfl)
  | [a], _, _, hp => by
      have hap : ∀ v : V, a ≤ p v := by
        intro v; rcases hp v with ⟨x, hx, hxp⟩; simp only [List.mem_singleton] at hx; linarith
      have hfa : Finset.univ.filter (fun v => a ≤ p v) = Finset.univ := by
        ext v; simp [hap v]
      have hfa' : Finset.univ.filter (fun v => a + alpha ≤ p v + alpha) = Finset.univ := by
        ext v; simp [hap v]
      simp only [List.map, lovaszList, hfa, hfa', hr]
      dsimp [PosScalarMul]
      exact_mod_cast (by ring : (a + alpha) * r = a * r + alpha * r)
  | a :: b :: rest, _, hpw, hp => by
      rcases List.pairwise_cons.mp hpw with ⟨ha_gt, hpw'⟩
      have hab : a > b := ha_gt b List.mem_cons_self
      have ih := lovaszList_map_add rho r hr p alpha (b :: rest) (by simp) hpw'
        (step_exists_le hab hp)
      have hsub : (a + alpha) - (b + alpha) = a - b := by ring
      have hfilt : Finset.univ.filter (fun v => a + alpha ≤ p v + alpha) =
          Finset.univ.filter (fun v => a ≤ p v) := by
        ext v; simp
      simp only [List.map] at ih
      simp only [List.map, lovaszList, hsub, hfilt, ih, add_assoc]

private lemma lovaszList_map_mul (rho : Finset V → WithTop ℝ) (p : V → ℝ) {t : ℝ} (ht : 0 < t) :
    ∀ (L : List ℝ),
      lovaszList rho (fun v => t * p v) (L.map (t * ·)) =
        PosScalarMul t (lovaszList rho p L)
  | [] => by simp [lovaszList, PosScalarMul]
  | [a] => by
      have hfilt : Finset.univ.filter (fun v => t * a ≤ t * p v) =
          Finset.univ.filter (fun v => a ≤ p v) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => le_of_mul_le_mul_left h ht, fun h => mul_le_mul_of_nonneg_left h (le_of_lt ht)⟩
      simp only [List.map, lovaszList, hfilt, posScalarMul_mul_pos ht]
  | a :: b :: rest => by
      have ih := lovaszList_map_mul rho p ht (b :: rest)
      have hsub : t * a - t * b = t * (a - b) := by ring
      have hfilt : Finset.univ.filter (fun v => t * a ≤ t * p v) =
          Finset.univ.filter (fun v => a ≤ p v) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => le_of_mul_le_mul_left h ht, fun h => mul_le_mul_of_nonneg_left h (le_of_lt ht)⟩
      simp only [List.map] at ih
      simp only [List.map, lovaszList, hsub, hfilt, ih, posScalarMul_mul_pos ht,
        posScalarMul_distrib_add ht]

private lemma lovasz_zeroLR (rho : Finset V → WithTop ℝ)
    (hrho : SubmodularSetFunction rho) :
    ZeroLR (LovaszExtension rho) := by
  by_cases hV : Nonempty V
  · have : Nonempty V := hV
    refine ⟨fun p q => ?_, ?_, fun p t ht => ?_⟩
    · set U := SortedValues p ++ SortedValues q
      have hU_mem : ∀ (f : V → ℝ), (∀ v : V, f v = p v ∨ f v = q v) →
          ∀ x, (x ∈ U ∨ x ∈ SortedValues f) ↔ x ∈ U := by
        intro f hf x
        refine ⟨fun hx => ?_, fun hx => Or.inl hx⟩
        rcases hx with hx | hx
        · exact hx
        · unfold SortedValues at hx
          rw [Finset.mem_sort, Finset.mem_image] at hx
          rcases hx with ⟨v, _, rfl⟩
          simp only [U, List.mem_append]
          rcases hf v with hfv | hfv
          · left; rw [hfv]; exact mem_sortedValues p v
          · right; rw [hfv]; exact mem_sortedValues q v
      rcases lovaszList_foldr_insLow rho hrho p U (SortedValues p)
        (sortedValues_ne_nil p) (pairwise_sortedValues p) (mem_sortedValues p) with
        ⟨heq_p, _, hpw_p, hmem_p⟩
      rcases lovaszList_foldr_insLow rho hrho q U (SortedValues q)
        (sortedValues_ne_nil q) (pairwise_sortedValues q) (mem_sortedValues q) with
        ⟨heq_q, _, hpw_q, hmem_q⟩
      rcases lovaszList_foldr_insLow rho hrho (p ⊔ q) U (SortedValues (p ⊔ q))
        (sortedValues_ne_nil (p ⊔ q)) (pairwise_sortedValues (p ⊔ q)) (mem_sortedValues (p ⊔ q)) with
        ⟨heq_sup, _, hpw_sup, hmem_sup⟩
      rcases lovaszList_foldr_insLow rho hrho (p ⊓ q) U (SortedValues (p ⊓ q))
        (sortedValues_ne_nil (p ⊓ q)) (pairwise_sortedValues (p ⊓ q)) (mem_sortedValues (p ⊓ q)) with
        ⟨heq_inf, _, hpw_inf, hmem_inf⟩
      set L := U.foldr insLow (SortedValues p)
      have hL_mem : ∀ x, x ∈ L ↔ x ∈ U := by
        intro x
        rw [hmem_p x]
        exact hU_mem p (fun v => Or.inl rfl) x
      have hLq : U.foldr insLow (SortedValues q) = L := by
        refine eq_of_pairwise_gt hpw_q hpw_p (fun x => ?_)
        rw [hmem_q x, hL_mem x]
        exact hU_mem q (fun v => Or.inr rfl) x
      have hLsup : U.foldr insLow (SortedValues (p ⊔ q)) = L := by
        refine eq_of_pairwise_gt hpw_sup hpw_p (fun x => ?_)
        rw [hmem_sup x, hL_mem x]
        exact hU_mem (p ⊔ q) (fun v => max_choice (p v) (q v)) x
      have hLinf : U.foldr insLow (SortedValues (p ⊓ q)) = L := by
        refine eq_of_pairwise_gt hpw_inf hpw_p (fun x => ?_)
        rw [hmem_inf x, hL_mem x]
        exact hU_mem (p ⊓ q) (fun v => min_choice (p v) (q v)) x
      rw [← lovaszList_sortedValues rho p, ← heq_p,
          ← lovaszList_sortedValues rho q, ← heq_q, hLq,
          ← lovaszList_sortedValues rho (p ⊔ q), ← heq_sup, hLsup,
          ← lovaszList_sortedValues rho (p ⊓ q), ← heq_inf, hLinf]
      exact lovaszList_sbfr rho hrho p q L hpw_p
        (fun v => ⟨p v, (hL_mem (p v)).mpr (List.mem_append_left _ (mem_sortedValues p v)), le_rfl⟩)
        (fun v => ⟨q v, (hL_mem (q v)).mpr (List.mem_append_right _ (mem_sortedValues q v)), le_rfl⟩)
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hrho.2.1
      refine ⟨r, fun p alpha => ?_⟩
      have hsort_shift : SortedValues (fun v => p v + alpha) = (SortedValues p).map (· + alpha) := by
        refine eq_of_pairwise_gt (pairwise_sortedValues _) ?_ (fun x => ?_)
        · rw [List.pairwise_map]
          refine List.Pairwise.imp ?_ (pairwise_sortedValues p)
          intro a b hab
          linarith
        · unfold SortedValues
          simp only [Finset.mem_sort, Finset.mem_image, Finset.mem_univ, true_and, List.mem_map]
          constructor
          · rintro ⟨v, rfl⟩
            exact ⟨p v, ⟨v, rfl⟩, rfl⟩
          · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
            exact ⟨v, rfl⟩
      rw [← lovaszList_sortedValues rho (fun v => p v + alpha),
          ← lovaszList_sortedValues rho p, hsort_shift]
      exact lovaszList_map_add rho r hr.symm p alpha (SortedValues p)
        (sortedValues_ne_nil p) (pairwise_sortedValues p)
        (fun v => ⟨p v, mem_sortedValues p v, le_rfl⟩)
    · have hsort_mul : SortedValues (fun v => t * p v) = (SortedValues p).map (t * ·) := by
        refine eq_of_pairwise_gt (pairwise_sortedValues _) ?_ (fun x => ?_)
        · rw [List.pairwise_map]
          refine List.Pairwise.imp ?_ (pairwise_sortedValues p)
          intro a b hab
          exact mul_lt_mul_of_pos_left hab ht
        · unfold SortedValues
          simp only [Finset.mem_sort, Finset.mem_image, Finset.mem_univ, true_and, List.mem_map]
          constructor
          · rintro ⟨v, rfl⟩
            exact ⟨p v, ⟨v, rfl⟩, rfl⟩
          · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
            exact ⟨v, rfl⟩
      rw [← lovaszList_sortedValues rho (fun v => t * p v),
          ← lovaszList_sortedValues rho p, hsort_mul]
      exact lovaszList_map_mul rho p ht (SortedValues p)
  · have : IsEmpty V := not_nonempty_iff.mp hV
    have hsort_nil : ∀ p : V → ℝ, SortedValues p = [] := by
      intro p
      unfold SortedValues
      simp [Finset.univ_eq_empty]
    have hlov_zero : ∀ p : V → ℝ, LovaszExtension rho p = 0 := by
      intro p
      rw [← lovaszList_sortedValues, hsort_nil]
      rfl
    refine ⟨fun p q => by simp [hlov_zero], ⟨0, fun p alpha => by simp [hlov_zero]⟩,
      fun p t _ => by simp [hlov_zero, PosScalarMul]⟩

private lemma lovasz_mconvex_eq (rho : Finset V → WithTop ℝ) :
    DiscreteConvex.MConvexSetsB.LovaszExtension rho = LovaszExtension rho := by
  ext p
  rfl

private lemma coe_untopD_of_ne_top {w : WithTop ℝ} (hw : w ≠ ⊤) :
    ((w.untopD 0 : ℝ) : WithTop ℝ) = w := by
  lift w to ℝ using hw with r
  rfl

private lemma scalarWithTop_mono {c : ℝ} (hc : 0 ≤ c) {z w : WithTop ℝ} (h : z ≤ w) :
    DiscreteConvex.MConvexSetsB.ScalarWithTop c z ≤ DiscreteConvex.MConvexSetsB.ScalarWithTop c w := by
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · cases z <;> cases w <;> simp [DiscreteConvex.MConvexSetsB.ScalarWithTop]
  · cases w with
    | top =>
      cases z <;> simp [DiscreteConvex.MConvexSetsB.ScalarWithTop, ne_of_gt hc_pos]
    | coe rw =>
      cases z with
      | top => exact False.elim (WithTop.not_top_le_coe rw h)
      | coe rz =>
        rw [WithTop.coe_le_coe] at h
        dsimp [DiscreteConvex.MConvexSetsB.ScalarWithTop]
        exact_mod_cast mul_le_mul_of_nonneg_left h hc

private lemma jensen_isConvexWithTop (f : (V → ℝ) → WithTop ℝ)
    (hf : DiscreteConvex.MConvexSetsB.IsConvexWithTop f)
    (S : Finset (V → ℤ)) :
    ∀ (lam : (V → ℤ) → ℝ) (z : (V → ℤ) → (V → ℝ)) (val : (V → ℤ) → ℝ),
      (∀ y ∈ S, 0 ≤ lam y) →
      (∑ y ∈ S, lam y = 1) →
      (∀ y ∈ S, f (z y) ≤ (val y : WithTop ℝ)) →
      f (fun v => ∑ y ∈ S, lam y * z y v) ≤ ((∑ y ∈ S, lam y * val y : ℝ) : WithTop ℝ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro lam _ _ _ h1 _
    simp at h1
  | @insert a S' ha ih =>
    intro lam z val h0 h1 hle
    have hsum_ins : lam a + ∑ y ∈ S', lam y = 1 := by
      rw [← Finset.sum_insert ha]
      exact h1
    have ha0 : 0 ≤ lam a := h0 a (Finset.mem_insert_self a S')
    have hS0 : ∀ y ∈ S', 0 ≤ lam y := fun y hy => h0 y (Finset.mem_insert_of_mem hy)
    have hsum_nonneg : 0 ≤ ∑ y ∈ S', lam y := Finset.sum_nonneg hS0
    rcases eq_or_lt_of_le hsum_nonneg with hsum_zero | hsum_pos
    · have hlam_zero : ∀ y ∈ S', lam y = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hS0).mp hsum_zero.symm
      have ha1 : lam a = 1 := by linarith
      have hpt : (fun v => ∑ y ∈ insert a S', lam y * z y v) = z a := by
        ext v
        rw [Finset.sum_insert ha, ha1, one_mul]
        have h0' : ∑ y ∈ S', lam y * z y v = 0 :=
          Finset.sum_eq_zero (fun y hy => by rw [hlam_zero y hy, zero_mul])
        linarith
      have hval : ∑ y ∈ insert a S', lam y * val y = val a := by
        rw [Finset.sum_insert ha, ha1, one_mul]
        have h0' : ∑ y ∈ S', lam y * val y = 0 :=
          Finset.sum_eq_zero (fun y hy => by rw [hlam_zero y hy, zero_mul])
        linarith
      rw [hpt, hval]
      exact hle a (Finset.mem_insert_self a S')
    · let s := ∑ y ∈ S', lam y
      have hs_pos : 0 < s := hsum_pos
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      let lam' : (V → ℤ) → ℝ := fun y => lam y / s
      have h0' : ∀ y ∈ S', 0 ≤ lam' y := fun y hy => div_nonneg (hS0 y hy) (le_of_lt hs_pos)
      have h1' : ∑ y ∈ S', lam' y = 1 := by
        dsimp [lam']
        rw [← Finset.sum_div]
        exact div_self hs_ne
      have hle' : ∀ y ∈ S', f (z y) ≤ (val y : WithTop ℝ) :=
        fun y hy => hle y (Finset.mem_insert_of_mem hy)
      have ih_step := ih lam' z val h0' h1' hle'
      let x' : V → ℝ := fun v => ∑ y ∈ S', lam' y * z y v
      have hcomb : (fun v => ∑ y ∈ insert a S', lam y * z y v) =
          (fun v => lam a * z a v + (1 - lam a) * x' v) := by
        ext v
        rw [Finset.sum_insert ha]
        have h1s : 1 - lam a = s := by linarith
        rw [h1s]
        congr 1
        dsimp [x', lam']
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        field_simp [hs_ne]
      rw [hcomb]
      have ha_le1 : lam a ≤ 1 := by linarith
      have hconv := hf (z a) x' (lam a) ha0 ha_le1
      have hsc1 := scalarWithTop_mono ha0 (hle a (Finset.mem_insert_self a S'))
      have hsc2 := scalarWithTop_mono (sub_nonneg.mpr ha_le1) ih_step
      refine hconv.trans ((add_le_add hsc1 hsc2).trans_eq ?_)
      dsimp only [DiscreteConvex.MConvexSetsB.ScalarWithTop]
      rw [← WithTop.coe_add, Finset.sum_insert ha]
      congr 1
      have h1s : 1 - lam a = s := by linarith
      rw [h1s]
      congr 1
      dsimp [lam']
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      field_simp [hs_ne]

private lemma lovasz_le_convexClosureValOn (rho : Finset V → WithTop ℝ)
    (hrho : SubmodularSetFunction rho) (S : Finset (V → ℤ)) (x : V → ℝ) :
    let g : (V → ℤ) → WithTop ℝ := fun p => LovaszExtension rho (fun v => (p v : ℝ))
    LovaszExtension rho x ≤ ConvexClosureValOn g S x := by
  intro g
  have hconv : DiscreteConvex.MConvexSetsB.IsConvexWithTop (LovaszExtension rho) := by
    rw [← lovasz_mconvex_eq]
    exact (DiscreteConvex.MConvexSetsB.lovasz_convex_iff_submodular rho hrho.1 hrho.2.1).mp hrho.2.2
  unfold ConvexClosureValOn
  let A := {val : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
    (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ g) ∧
    (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
    val = ((∑ y ∈ S, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)}
  rcases A.eq_empty_or_nonempty with hA_empty | hA_ne
  · change LovaszExtension rho x ≤ sInf A
    rw [hA_empty, WithTop.sInf_empty]
    exact le_top
  apply le_csInf hA_ne
  rintro val ⟨lam, h0, h1, hdom, hbary, rfl⟩
  have hle_y : ∀ y ∈ S, LovaszExtension rho (fun v => (y v : ℝ)) ≤ (((g y).untopD 0 : ℝ) : WithTop ℝ) := by
    intro y hy
    rw [coe_untopD_of_ne_top (hdom y hy)]
  have hj := jensen_isConvexWithTop (LovaszExtension rho) hconv S lam
    (fun y v => (y v : ℝ)) (fun y => (g y).untopD 0) h0 h1 hle_y
  have hx_eq : (fun v => ∑ y ∈ S, lam y * (y v : ℝ)) = x := by
    ext v; exact hbary v
  rw [hx_eq] at hj
  exact hj

private lemma bddBelow_convexClosureVal (rho : Finset V → WithTop ℝ)
    (hrho : SubmodularSetFunction rho) (x : V → ℝ) :
    let g : (V → ℤ) → WithTop ℝ := fun p => LovaszExtension rho (fun v => (p v : ℝ))
    BddBelow {L : WithTop ℝ | ∃ (S : Finset (V → ℤ)),
      (∀ y ∈ S, y ∈ DomZ g) ∧ L = ConvexClosureValOn g S x} := by
  intro g
  refine ⟨LovaszExtension rho x, ?_⟩
  rintro L ⟨S, _, rfl⟩
  exact lovasz_le_convexClosureValOn rho hrho S x

private lemma lovasz_le_convexClosureVal (rho : Finset V → WithTop ℝ)
    (hrho : SubmodularSetFunction rho) (x : V → ℝ) :
    let g : (V → ℤ) → WithTop ℝ := fun p => LovaszExtension rho (fun v => (p v : ℝ))
    LovaszExtension rho x ≤ ConvexClosureVal g x := by
  intro g
  unfold ConvexClosureVal
  let B := {L : WithTop ℝ | ∃ (S : Finset (V → ℤ)),
    (∀ y ∈ S, y ∈ DomZ g) ∧ L = ConvexClosureValOn g S x}
  rcases B.eq_empty_or_nonempty with hB_empty | hB_ne
  · change LovaszExtension rho x ≤ sInf B
    rw [hB_empty, WithTop.sInf_empty]
    exact le_top
  apply le_csInf hB_ne
  rintro L ⟨S, _, rfl⟩
  exact lovasz_le_convexClosureValOn rho hrho S x

private noncomputable def stepPt (m M : ℤ) (z : V → ℝ) (a : ℝ) : V → ℤ :=
  fun v => m + if a ≤ z v then M else 0

private noncomputable def stepListSum (g : (V → ℤ) → WithTop ℝ) (m M : ℤ) (z : V → ℝ) : List ℝ → WithTop ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
      PosScalarMul (a - b) (g (stepPt m M z a)) + stepListSum g m M z (b :: rest)

private noncomputable def lamStep (m M : ℤ) (z : V → ℝ) : List ℝ → (V → ℤ) → ℝ
  | [], _ => 0
  | [_], _ => 0
  | a :: b :: rest, w =>
      (if w = stepPt m M z a then a - b else 0) + lamStep m M z (b :: rest) w

private lemma lamStep_nonneg (m M : ℤ) (z : V → ℝ) :
    ∀ (L : List ℝ), List.Pairwise (· > ·) L → ∀ w : V → ℤ, 0 ≤ lamStep m M z L w
  | [], _, _ => le_rfl
  | [_], _, _ => le_rfl
  | a :: b :: rest, hpw, w => by
      rcases List.pairwise_cons.mp hpw with ⟨ha, hpw'⟩
      have hab : 0 ≤ a - b := le_of_lt (sub_pos.mpr (ha b List.mem_cons_self))
      simp only [lamStep]
      apply add_nonneg
      · split_ifs <;> linarith
      · exact lamStep_nonneg m M z (b :: rest) hpw' w

private lemma sum_lamStep_mul (g : (V → ℤ) → WithTop ℝ) (m M : ℤ) (z : V → ℝ)
    (S : Finset (V → ℤ)) (F : (V → ℤ) → ℝ) :
    ∀ (L : List ℝ), List.Pairwise (· > ·) L →
      (∀ a ∈ L, stepPt m M z a ∈ DomZ g → stepPt m M z a ∈ S) →
      stepListSum g m M z L ≠ ⊤ →
      ∑ w ∈ S, lamStep m M z L w * F w =
        match L with
        | [] => 0
        | [_] => 0
        | a :: b :: rest =>
            (a - b) * F (stepPt m M z a) + ∑ w ∈ S, lamStep m M z (b :: rest) w * F w
  | [], _, _, _ => by simp [lamStep]
  | [_], _, _, _ => by simp [lamStep]
  | a :: b :: rest, hpw, hS, hne_top => by
      rcases List.pairwise_cons.mp hpw with ⟨ha, _⟩
      have hab_lt : b < a := ha b List.mem_cons_self
      have hab_ne : a - b ≠ 0 := ne_of_gt (sub_pos.mpr hab_lt)
      simp only [stepListSum] at hne_top
      have hhead_ne_top : PosScalarMul (a - b) (g (stepPt m M z a)) ≠ ⊤ :=
        fun htop => hne_top (by simp [htop])
      have hdom_a : stepPt m M z a ∈ DomZ g := by
        intro htop
        apply hhead_ne_top
        simp [PosScalarMul, htop, hab_ne]
      have ha_S : stepPt m M z a ∈ S := hS a List.mem_cons_self hdom_a
      simp only [lamStep, add_mul, Finset.sum_add_distrib]
      congr 1
      have hite : (∑ w ∈ S, (if w = stepPt m M z a then a - b else 0) * F w) =
          ∑ w ∈ S, if w = stepPt m M z a then (a - b) * F w else 0 := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        split_ifs <;> ring
      rw [hite, Finset.sum_ite_eq' S (stepPt m M z a), if_pos ha_S]

private lemma sum_lamStep_const (g : (V → ℤ) → WithTop ℝ) (m M : ℤ) (z : V → ℝ)
    (S : Finset (V → ℤ)) :
    ∀ (L : List ℝ), L ≠ [] → List.Pairwise (· > ·) L →
      (∀ a ∈ L, stepPt m M z a ∈ DomZ g → stepPt m M z a ∈ S) →
      stepListSum g m M z L ≠ ⊤ →
      ∑ w ∈ S, lamStep m M z L w * (1 : ℝ) = L.headD 0 - L.getLastD 0
  | [], hne, _, _, _ => False.elim (hne rfl)
  | [a], _, _, _, _ => by simp [lamStep]
  | a :: b :: rest, _, hpw, hS, hne_top => by
      rcases List.pairwise_cons.mp hpw with ⟨_, hpw'⟩
      have hS' : ∀ c ∈ b :: rest, stepPt m M z c ∈ DomZ g → stepPt m M z c ∈ S :=
        fun c hc => hS c (List.mem_cons_of_mem a hc)
      have hne_top' : stepListSum g m M z (b :: rest) ≠ ⊤ :=
        fun htop => hne_top (by simp [stepListSum, htop])
      rw [sum_lamStep_mul g m M z S (fun _ => 1) (a :: b :: rest) hpw hS hne_top]
      dsimp only
      rw [sum_lamStep_const g m M z S (b :: rest) (by simp) hpw' hS' hne_top']
      simp only [mul_one, List.headD_cons, List.getLastD_cons]
      ring

private lemma sum_lamStep_coord (g : (V → ℤ) → WithTop ℝ) (m M : ℤ) (z : V → ℝ)
    (S : Finset (V → ℤ)) (v : V) :
    ∀ (L : List ℝ), L ≠ [] → List.Pairwise (· > ·) L →
      (∀ a ∈ L, stepPt m M z a ∈ DomZ g → stepPt m M z a ∈ S) →
      stepListSum g m M z L ≠ ⊤ →
      (z v ∈ L →
        ∑ w ∈ S, lamStep m M z L w * (w v : ℝ) =
          (L.headD 0 - L.getLastD 0) * (m : ℝ) + (M : ℝ) * (z v - L.getLastD 0)) ∧
      ((∀ c ∈ L, c < z v) →
        ∑ w ∈ S, lamStep m M z L w * (w v : ℝ) =
          (L.headD 0 - L.getLastD 0) * ((m : ℝ) + (M : ℝ))) := by
  intro L hne hpw hS hne_top
  induction L with
  | nil => exact False.elim (hne rfl)
  | cons a tail ih =>
    cases tail with
    | nil =>
      refine ⟨fun hmem => ?_, fun _ => ?_⟩
      · simp only [List.mem_singleton] at hmem
        simp [lamStep, ← hmem]
      · simp [lamStep]
    | cons b rest =>
      rcases List.pairwise_cons.mp hpw with ⟨ha_gt, hpw'⟩
      have hS' : ∀ c ∈ b :: rest, stepPt m M z c ∈ DomZ g → stepPt m M z c ∈ S :=
        fun c hc => hS c (List.mem_cons_of_mem a hc)
      have hne_top' : stepListSum g m M z (b :: rest) ≠ ⊤ :=
        fun htop => hne_top (by simp [stepListSum, htop])
      rcases ih (by simp) hpw' hS' hne_top' with ⟨ih_mem, ih_lt⟩
      rw [sum_lamStep_mul g m M z S (fun w => (w v : ℝ)) (a :: b :: rest) hpw hS hne_top]
      dsimp only
      refine ⟨fun hmem => ?_, fun hlt => ?_⟩
      · rcases List.mem_cons.mp hmem with h_eq | hmem'
        · have hlt' : ∀ c ∈ b :: rest, c < z v := by
            intro c hc; rw [h_eq]; exact ha_gt c hc
          rw [ih_lt hlt']
          have hr_a : (stepPt m M z a v : ℝ) = (m : ℝ) + (M : ℝ) := by
            dsimp only [stepPt]
            rw [if_pos (le_of_eq h_eq.symm)]
            push_cast; ring
          rw [hr_a, h_eq]
          simp only [List.headD_cons, List.getLastD_cons]
          ring
        · rw [ih_mem hmem']
          have h_gt : z v < a := ha_gt _ hmem'
          have hr_a : (stepPt m M z a v : ℝ) = (m : ℝ) := by
            dsimp only [stepPt]
            rw [if_neg (not_le_of_gt h_gt)]
            push_cast; ring
          rw [hr_a]
          simp only [List.headD_cons, List.getLastD_cons]
          ring
      · have hlt' : ∀ c ∈ b :: rest, c < z v :=
          fun c hc => hlt c (List.mem_cons_of_mem a hc)
        rw [ih_lt hlt']
        have ha_lt : a < z v := hlt a List.mem_cons_self
        have hr_a : (stepPt m M z a v : ℝ) = (m : ℝ) + (M : ℝ) := by
          dsimp only [stepPt]
          rw [if_pos (le_of_lt ha_lt)]
          push_cast; ring
        rw [hr_a]
        simp only [List.headD_cons, List.getLastD_cons]
        ring

private lemma sum_lamStep_g (g : (V → ℤ) → WithTop ℝ) (m M : ℤ) (z : V → ℝ)
    (S : Finset (V → ℤ)) :
    ∀ (L : List ℝ), List.Pairwise (· > ·) L →
      (∀ a ∈ L, stepPt m M z a ∈ DomZ g → stepPt m M z a ∈ S) →
      stepListSum g m M z L ≠ ⊤ →
      ((∑ w ∈ S, lamStep m M z L w * (g w).untopD 0 : ℝ) : WithTop ℝ) = stepListSum g m M z L
  | [], _, _, _ => by simp [lamStep, stepListSum]
  | [_], _, _, _ => by simp [lamStep, stepListSum]
  | a :: b :: rest, hpw, hS, hne_top => by
      rcases List.pairwise_cons.mp hpw with ⟨ha_gt, hpw'⟩
      have hab_lt : b < a := ha_gt b List.mem_cons_self
      have hab_ne : a - b ≠ 0 := ne_of_gt (sub_pos.mpr hab_lt)
      have hS' : ∀ c ∈ b :: rest, stepPt m M z c ∈ DomZ g → stepPt m M z c ∈ S :=
        fun c hc => hS c (List.mem_cons_of_mem a hc)
      have hne_top' : stepListSum g m M z (b :: rest) ≠ ⊤ :=
        fun htop => hne_top (by simp [stepListSum, htop])
      have hhead_ne_top : PosScalarMul (a - b) (g (stepPt m M z a)) ≠ ⊤ :=
        fun htop => hne_top (by simp [stepListSum, htop])
      have hdom_a : g (stepPt m M z a) ≠ ⊤ := by
        intro htop
        apply hhead_ne_top
        simp [PosScalarMul, htop, hab_ne]
      rw [sum_lamStep_mul g m M z S (fun w => (g w).untopD 0) (a :: b :: rest) hpw hS hne_top]
      dsimp only
      rw [WithTop.coe_add, sum_lamStep_g g m M z S (b :: rest) hpw' hS' hne_top']
      simp only [stepListSum]
      congr 1
      lift g (stepPt m M z a) to ℝ using hdom_a with r hr
      simp [PosScalarMul]

private lemma g_stepPt_eq [Nonempty V] (rho : Finset V → WithTop ℝ) (hrho : SubmodularSetFunction rho)
    (r : ℝ) (hr : rho Finset.univ = (r : WithTop ℝ))
    (m M : ℤ) (hM : 0 < (M : ℝ)) (z : V → ℝ) (a : ℝ) :
    LovaszExtension rho (fun v => (stepPt m M z a v : ℝ)) =
      PosScalarMul (M : ℝ) (rho (Finset.univ.filter (fun v => a ≤ z v))) +
        (((m : ℝ) * r : ℝ) : WithTop ℝ) := by
  have hcast : (fun v => (stepPt m M z a v : ℝ)) =
      (fun v => (if a ≤ z v then (M : ℝ) else 0) + (m : ℝ)) := by
    ext v
    dsimp [stepPt]
    split_ifs <;> push_cast <;> ring
  rw [hcast]
  have hsort_shift : SortedValues (fun v => (if a ≤ z v then (M : ℝ) else 0) + (m : ℝ)) =
      (SortedValues (fun v => if a ≤ z v then (M : ℝ) else 0)).map (· + (m : ℝ)) := by
    refine eq_of_pairwise_gt (pairwise_sortedValues _) ?_ (fun x => ?_)
    · rw [List.pairwise_map]
      refine List.Pairwise.imp ?_ (pairwise_sortedValues _)
      intro c d hcd; linarith
    · unfold SortedValues
      simp only [Finset.mem_sort, Finset.mem_image, Finset.mem_univ, true_and, List.mem_map]
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨_, ⟨v, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
        exact ⟨v, rfl⟩
  rw [← lovaszList_sortedValues rho (fun v => (if a ≤ z v then (M : ℝ) else 0) + (m : ℝ)),
      hsort_shift,
      lovaszList_map_add rho r hr (fun v => if a ≤ z v then (M : ℝ) else 0) (m : ℝ)
        (SortedValues _) (sortedValues_ne_nil _) (pairwise_sortedValues _)
        (fun v => ⟨_, mem_sortedValues _ v, le_rfl⟩),
      lovaszList_sortedValues]
  congr 1
  have hpwM0 : List.Pairwise (· > ·) ([(M : ℝ), 0] : List ℝ) := by
    simp [hM]
  have hmemM0 : ∀ v : V, (if a ≤ z v then (M : ℝ) else 0) ∈ ([(M : ℝ), 0] : List ℝ) := by
    intro v
    split_ifs <;> simp
  rw [lovasz_eq_lovaszList_of_mem rho hrho _ [(M : ℝ), 0] hpwM0 hmemM0]
  simp only [lovaszList, sub_zero, posScalarMul_zero, add_zero]
  congr 2
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h
  · simp [h]
  · simp [h, not_le.mpr hM]

private lemma stepListSum_eq_lovaszList [Nonempty V] (rho : Finset V → WithTop ℝ)
    (hrho : SubmodularSetFunction rho) (r : ℝ) (hr : rho Finset.univ = (r : WithTop ℝ))
    (m M : ℤ) (hM : 0 < (M : ℝ)) (z : V → ℝ) :
    let g : (V → ℤ) → WithTop ℝ := fun p => LovaszExtension rho (fun v => (p v : ℝ))
    ∀ (L : List ℝ), L ≠ [] → List.Pairwise (· > ·) L → L.getLastD 0 = 0 →
      stepListSum g m M z L =
        PosScalarMul (M : ℝ) (lovaszList rho z L) +
          (((L.headD 0 - L.getLastD 0) * ((m : ℝ) * r) : ℝ) : WithTop ℝ) := by
  intro g L hne hpw hlast
  induction L with
  | nil => exact False.elim (hne rfl)
  | cons a tail ih =>
    cases tail with
    | nil =>
      change a = 0 at hlast
      subst hlast
      simp only [stepListSum, lovaszList, posScalarMul_zero]
      have h0 : PosScalarMul (M : ℝ) 0 = 0 := by simp [PosScalarMul]
      simp [h0]
    | cons b rest =>
      rcases List.pairwise_cons.mp hpw with ⟨ha_gt, hpw'⟩
      have hab : 0 < a - b := sub_pos.mpr (ha_gt b List.mem_cons_self)
      have hlast' : (b :: rest).getLastD 0 = 0 := hlast
      have ih_step := ih (by simp) hpw' hlast'
      simp only [stepListSum, lovaszList, ih_step]
      have hg_a : g (stepPt m M z a) =
          PosScalarMul (M : ℝ) (rho (Finset.univ.filter (fun v => a ≤ z v))) +
            (((m : ℝ) * r : ℝ) : WithTop ℝ) :=
        g_stepPt_eq rho hrho r hr m M hM z a
      rw [hg_a, posScalarMul_distrib_add hab, ← posScalarMul_mul_pos hab,
          mul_comm (a - b) (M : ℝ), posScalarMul_mul_pos hM,
          posScalarMul_distrib_add hM]
      have hcoe : PosScalarMul (a - b) (((m : ℝ) * r : ℝ) : WithTop ℝ) =
          (((a - b) * ((m : ℝ) * r) : ℝ) : WithTop ℝ) := rfl
      have hhead_ab : (a :: b :: rest).headD 0 = a := rfl
      have hlast_ab : (a :: b :: rest).getLastD 0 = (b :: rest).getLastD 0 := rfl
      have hhead_b : (b :: rest).headD 0 = b := rfl
      rw [hcoe, hhead_ab, hlast_ab, hhead_b]
      have hdecomp : (((a - (b :: rest).getLastD 0) * ((m : ℝ) * r) : ℝ) : WithTop ℝ) =
          (((a - b) * ((m : ℝ) * r) : ℝ) : WithTop ℝ) +
            (((b - (b :: rest).getLastD 0) * ((m : ℝ) * r) : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add]
        congr 1
        ring
      rw [hdecomp]
      ac_rfl

private lemma getLastD_eq_getLast_of_ne_nil :
    ∀ (L : List ℝ) (hne : L ≠ []), L.getLastD 0 = L.getLast hne
  | [], hne => False.elim (hne rfl)
  | [a], _ => rfl
  | a :: b :: rest, _ => getLastD_eq_getLast_of_ne_nil (b :: rest) (by simp)

private lemma bddBelow_convexClosureValOn (g : (V → ℤ) → WithTop ℝ)
    (S : Finset (V → ℤ)) (x : V → ℝ) :
    BddBelow {val : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
      (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ g) ∧
      (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
      val = ((∑ y ∈ S, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)} := by
  refine ⟨((∑ y ∈ S, -|(g y).untopD 0| : ℝ) : WithTop ℝ), ?_⟩
  rintro val ⟨lam, h0, h1, _, _, rfl⟩
  rw [WithTop.coe_le_coe]
  refine Finset.sum_le_sum (fun y hy => ?_)
  have hle1 : lam y ≤ 1 := by
    have : lam y ≤ ∑ z ∈ S, lam z := Finset.single_le_sum h0 hy
    linarith
  have hneg : -|(g y).untopD 0| ≤ (g y).untopD 0 := neg_abs_le _
  have habs : 0 ≤ |(g y).untopD 0| := abs_nonneg _
  nlinarith [h0 y hy]

private lemma convexClosureVal_le_lovasz [Nonempty V] (rho : Finset V → WithTop ℝ)
    (hrho : SubmodularSetFunction rho) (x : V → ℝ) :
    let g : (V → ℤ) → WithTop ℝ := fun p => LovaszExtension rho (fun v => (p v : ℝ))
    ConvexClosureVal g x ≤ LovaszExtension rho x := by
  intro g
  by_cases htop : LovaszExtension rho x = ⊤
  · rw [htop]; exact le_top
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hrho.2.1
  let m : ℤ := Finset.univ.inf' Finset.univ_nonempty (fun v => ⌊x v⌋)
  have hm_le : ∀ v : V, (m : ℝ) ≤ x v := by
    intro v
    have h1 : m ≤ ⌊x v⌋ := Finset.inf'_le (fun u => ⌊x u⌋) (Finset.mem_univ v)
    have h2 : (m : ℝ) ≤ (⌊x v⌋ : ℝ) := by exact_mod_cast h1
    exact h2.trans (Int.floor_le (x v))
  let M : ℤ := max 1 (Finset.univ.sup' Finset.univ_nonempty (fun v => ⌈x v - (m : ℝ)⌉))
  have hM_ge1 : (1 : ℤ) ≤ M := le_max_left 1 _
  have hM_pos : (0 : ℝ) < (M : ℝ) := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge1
    linarith
  have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_pos
  have hx_le_M : ∀ v : V, x v - (m : ℝ) ≤ (M : ℝ) := by
    intro v
    have h1 : ⌈x v - (m : ℝ)⌉ ≤ M :=
      (Finset.le_sup' (fun u => ⌈x u - (m : ℝ)⌉) (Finset.mem_univ v)).trans (le_max_right 1 _)
    have h2 : (⌈x v - (m : ℝ)⌉ : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1
    exact (Int.le_ceil (x v - (m : ℝ))).trans h2
  let z : V → ℝ := fun v => (x v - (m : ℝ)) / (M : ℝ)
  have hz0 : ∀ v : V, 0 ≤ z v := fun v =>
    div_nonneg (sub_nonneg.mpr (hm_le v)) (le_of_lt hM_pos)
  have hz1 : ∀ v : V, z v ≤ 1 := fun v =>
    (div_le_one hM_pos).mpr (hx_le_M v)
  have hzx : ∀ v : V, (m : ℝ) + (M : ℝ) * z v = x v := by
    intro v
    dsimp [z]
    rw [mul_div_cancel₀ _ hM_ne]
    ring
  let S_vals : Finset ℝ := insert 1 (insert 0 (Finset.univ.image z))
  let L : List ℝ := S_vals.sort (· ≥ ·)
  have h1_mem : (1 : ℝ) ∈ L :=
    (Finset.mem_sort (· ≥ ·)).mpr (Finset.mem_insert_self 1 _)
  have h0_mem : (0 : ℝ) ∈ L :=
    (Finset.mem_sort (· ≥ ·)).mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self 0 _))
  have hne : L ≠ [] := List.ne_nil_of_mem h1_mem
  have hpw : List.Pairwise (· > ·) L := pairwise_gt_sort S_vals
  have hbounds : ∀ c ∈ L, 0 ≤ c ∧ c ≤ 1 := by
    intro c hc
    have hcS : c ∈ S_vals := (Finset.mem_sort (· ≥ ·)).mp hc
    rcases Finset.mem_insert.mp hcS with rfl | hcS
    · exact ⟨by norm_num, by norm_num⟩
    · rcases Finset.mem_insert.mp hcS with rfl | hcS
      · exact ⟨by norm_num, by norm_num⟩
      · rcases Finset.mem_image.mp hcS with ⟨v, _, rfl⟩
        exact ⟨hz0 v, hz1 v⟩
  have hhead : L.headD 0 = 1 := by
    cases hL : L with
    | nil => exact False.elim (hne hL)
    | cons a rest =>
      simp only [List.headD_cons]
      have ha_mem : a ∈ L := by rw [hL]; exact List.mem_cons_self
      have ha_le1 : a ≤ 1 := (hbounds a ha_mem).2
      have h1_in : (1 : ℝ) ∈ a :: rest := by rw [← hL]; exact h1_mem
      rcases List.mem_cons.mp h1_in with rfl | h1_rest
      · rfl
      · rw [hL] at hpw
        have ha_gt1 : a > 1 := (List.pairwise_cons.mp hpw).1 1 h1_rest
        linarith
  have hlast : L.getLastD 0 = 0 := by
    have hlast_mem : L.getLast hne ∈ L := List.getLast_mem hne
    have hlast_eq : L.getLastD 0 = L.getLast hne := getLastD_eq_getLast_of_ne_nil L hne
    rw [hlast_eq]
    have hge0 : 0 ≤ L.getLast hne := (hbounds _ hlast_mem).1
    by_contra hne0
    have hgt0 : 0 < L.getLast hne := lt_of_le_of_ne hge0 (Ne.symm hne0)
    rw [List.mem_iff_getElem] at h0_mem
    rcases h0_mem with ⟨i, hi, hLi⟩
    have hlast_idx : L.getLast hne = L[L.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hne) (by omega)) :=
      List.getLast_eq_getElem hne
    by_cases hi_last : i = L.length - 1
    · subst hi_last
      rw [hlast_idx, hLi] at hgt0
      exact lt_irrefl 0 hgt0
    · have hi_lt : i < L.length - 1 := by omega
      rw [List.pairwise_iff_getElem] at hpw
      have hgt := hpw i (L.length - 1) hi (Nat.sub_lt (List.length_pos_of_ne_nil hne) (by omega)) hi_lt
      rw [hLi, ← hlast_idx] at hgt
      linarith
  have hmem_z : ∀ v : V, z v ∈ L := by
    intro v
    rw [Finset.mem_sort]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem z (Finset.mem_univ v)))
  have hstep_eq : stepListSum g m M z L = LovaszExtension rho x := by
    rw [stepListSum_eq_lovaszList rho hrho r hr.symm m M hM_pos z L hne hpw hlast,
        hhead, hlast, sub_zero, one_mul,
        ← lovasz_eq_lovaszList_of_mem rho hrho z L hpw hmem_z]
    have h0L := lovasz_zeroLR rho hrho
    have hpos_z : PosScalarMul (M : ℝ) (LovaszExtension rho z) =
        LovaszExtension rho (fun v => (M : ℝ) * z v) :=
      (h0L.2.2 z (M : ℝ) hM_pos).symm
    rw [hpos_z]
    have hsort_shift : SortedValues (fun v => (M : ℝ) * z v + (m : ℝ)) =
        (SortedValues (fun v => (M : ℝ) * z v)).map (· + (m : ℝ)) := by
      refine eq_of_pairwise_gt (pairwise_sortedValues _) ?_ (fun c => ?_)
      · rw [List.pairwise_map]
        refine List.Pairwise.imp ?_ (pairwise_sortedValues _)
        intro a b hab; linarith
      · unfold SortedValues
        simp only [Finset.mem_sort, Finset.mem_image, Finset.mem_univ, true_and, List.mem_map]
        constructor
        · rintro ⟨v, rfl⟩
          exact ⟨_, ⟨v, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
          exact ⟨v, rfl⟩
    rw [← lovaszList_sortedValues rho (fun v => (M : ℝ) * z v),
        ← lovaszList_map_add rho r hr.symm (fun v => (M : ℝ) * z v) (m : ℝ)
          (SortedValues _) (sortedValues_ne_nil _) (pairwise_sortedValues _)
          (fun v => ⟨_, mem_sortedValues _ v, le_rfl⟩),
        ← hsort_shift, lovaszList_sortedValues]
    congr 1
    ext v
    linarith [hzx v]
  have hstep_ne_top : stepListSum g m M z L ≠ ⊤ := by
    rw [hstep_eq]; exact htop
  let S : Finset (V → ℤ) := (L.map (stepPt m M z)).toFinset.filter (fun w => w ∈ DomZ g)
  have hS_dom : ∀ w ∈ S, w ∈ DomZ g := fun w hw => (Finset.mem_filter.mp hw).2
  have hS_mem : ∀ a ∈ L, stepPt m M z a ∈ DomZ g → stepPt m M z a ∈ S := by
    intro a ha hdom
    rw [Finset.mem_filter, List.mem_toFinset]
    exact ⟨List.mem_map_of_mem ha, hdom⟩
  rw [← hstep_eq, ← sum_lamStep_g g m M z S L hpw hS_mem hstep_ne_top]
  have hle1 : ConvexClosureVal g x ≤ ConvexClosureValOn g S x := by
    unfold ConvexClosureVal
    exact csInf_le (bddBelow_convexClosureVal rho hrho x) ⟨S, hS_dom, rfl⟩
  refine hle1.trans ?_
  unfold ConvexClosureValOn
  apply csInf_le (bddBelow_convexClosureValOn g S x)
  refine ⟨lamStep m M z L, ?_, ?_, hS_dom, ?_, rfl⟩
  · intro w _
    exact lamStep_nonneg m M z L hpw w
  · have hsum := sum_lamStep_const g m M z S L hne hpw hS_mem hstep_ne_top
    simp only [mul_one, hhead, hlast, sub_zero] at hsum
    exact hsum
  · intro v
    have hcoord := (sum_lamStep_coord g m M z S v L hne hpw hS_mem hstep_ne_top).1 (hmem_z v)
    rw [hhead, hlast, sub_zero, one_mul, sub_zero] at hcoord
    rw [hcoord, hzx v]

private lemma isIntegerValued_posScalarMul {m : ℤ} {w : WithTop ℝ}
    (hw : ∃ k : ℤ, w = ((k : ℝ) : WithTop ℝ)) :
    ∃ k : ℤ, PosScalarMul (m : ℝ) w = ((k : ℝ) : WithTop ℝ) := by
  rcases hw with ⟨k, rfl⟩
  refine ⟨m * k, ?_⟩
  dsimp [PosScalarMul]
  push_cast
  rfl

private lemma isIntegerValued_add {w₁ w₂ : WithTop ℝ}
    (h1 : ∃ k : ℤ, w₁ = ((k : ℝ) : WithTop ℝ))
    (h2 : ∃ k : ℤ, w₂ = ((k : ℝ) : WithTop ℝ)) :
    ∃ k : ℤ, w₁ + w₂ = ((k : ℝ) : WithTop ℝ) := by
  rcases h1 with ⟨k₁, rfl⟩
  rcases h2 with ⟨k₂, rfl⟩
  refine ⟨k₁ + k₂, ?_⟩
  rw [← WithTop.coe_add]
  push_cast
  rfl

private lemma lovaszList_isIntegerValued (rho : Finset V → WithTop ℝ)
    (hint : IsIntegerValued rho) (p : V → ℝ) :
    ∀ (L : List ℝ), (∀ a ∈ L, ∃ m : ℤ, a = (m : ℝ)) →
      ∃ k : ℤ, lovaszList rho p L = ((k : ℝ) : WithTop ℝ)
  | [], _ => ⟨0, by simp [lovaszList]⟩
  | [a], hL => by
      rcases hL a List.mem_cons_self with ⟨m, rfl⟩
      exact isIntegerValued_posScalarMul (hint _)
  | a :: b :: rest, hL => by
      rcases hL a List.mem_cons_self with ⟨m_a, rfl⟩
      rcases hL b (List.mem_cons_of_mem _ List.mem_cons_self) with ⟨m_b, rfl⟩
      have hsub : ((m_a : ℝ) - (m_b : ℝ)) = ((m_a - m_b : ℤ) : ℝ) := by push_cast; ring
      simp only [lovaszList, hsub]
      refine isIntegerValued_add (isIntegerValued_posScalarMul (hint _))
        (lovaszList_isIntegerValued rho hint p ((m_b : ℝ) :: rest)
          (fun c hc => hL c (List.mem_cons_of_mem _ hc)))

theorem solution :
    (∀ rho : Finset V → WithTop ℝ, SubmodularSetFunction rho → ZeroLR (LovaszExtension rho)) ∧
    (∀ rho : Finset V → WithTop ℝ, SubmodularSetFunction rho → IsIntegerValued rho →
      ZeroLZZ (fun p : V → ℤ => LovaszExtension rho (fun v => (p v : ℝ)))) := by
  refine ⟨fun rho hrho => lovasz_zeroLR rho hrho, fun rho hrho hint => ?_⟩
  have h0LR := lovasz_zeroLR rho hrho
  let g : (V → ℤ) → WithTop ℝ := fun p => LovaszExtension rho (fun v => (p v : ℝ))
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro p q
    have hsup : (fun v => ((p ⊔ q) v : ℝ)) = (fun v => (p v : ℝ)) ⊔ (fun v => (q v : ℝ)) := by
      ext v; simp [Pi.sup_apply]
    have hinf : (fun v => ((p ⊓ q) v : ℝ)) = (fun v => (p v : ℝ)) ⊓ (fun v => (q v : ℝ)) := by
      ext v; simp [Pi.inf_apply]
    change LovaszExtension rho (fun v => (p v : ℝ)) + LovaszExtension rho (fun v => (q v : ℝ)) ≥
      LovaszExtension rho (fun v => ((p ⊔ q) v : ℝ)) + LovaszExtension rho (fun v => ((p ⊓ q) v : ℝ))
    rw [hsup, hinf]
    exact h0LR.1 (fun v => (p v : ℝ)) (fun v => (q v : ℝ))
  · rcases h0LR.2.1 with ⟨r, hr⟩
    refine ⟨r, fun p => ?_⟩
    change LovaszExtension rho (fun v => ((p + 1) v : ℝ)) =
      LovaszExtension rho (fun v => (p v : ℝ)) + (r : WithTop ℝ)
    have h1 : (fun v => ((p + 1) v : ℝ)) = (fun v => (p v : ℝ) + 1) := by
      ext v; simp [Pi.add_apply]
    rw [h1, hr (fun v => (p v : ℝ)) 1]
    simp
  · intro x t ht
    change ConvexClosureVal g (fun v => t * x v) = PosScalarMul t (ConvexClosureVal g x)
    by_cases hV : Nonempty V
    · have : Nonempty V := hV
      have hcc_eq : ∀ y : V → ℝ, ConvexClosureVal g y = LovaszExtension rho y :=
        fun y => le_antisymm (convexClosureVal_le_lovasz rho hrho y)
          (lovasz_le_convexClosureVal rho hrho y)
      rw [hcc_eq, hcc_eq]
      exact h0LR.2.2 x t ht
    · have : IsEmpty V := not_nonempty_iff.mp hV
      have htx : (fun v => t * x v) = x := Subsingleton.elim _ _
      rw [htx]
      have hsort_nil : ∀ y : V → ℝ, SortedValues y = [] := by
        intro y; unfold SortedValues; simp [Finset.univ_eq_empty]
      have hlov_zero : ∀ y : V → ℝ, LovaszExtension rho y = 0 := by
        intro y; rw [← lovaszList_sortedValues, hsort_nil]; rfl
      have hg_zero : ∀ p : V → ℤ, g p = 0 := fun p => hlov_zero _
      have hcc_zero : ConvexClosureVal g x = 0 := by
        apply le_antisymm
        · unfold ConvexClosureVal
          have h0_dom : ∀ y ∈ ({0} : Finset (V → ℤ)), y ∈ DomZ g := by
            intro y _; simp [DomZ, hg_zero y]
          refine (csInf_le (bddBelow_convexClosureVal rho hrho x) ⟨{0}, h0_dom, rfl⟩).trans ?_
          unfold ConvexClosureValOn
          refine (csInf_le (bddBelow_convexClosureValOn g {0} x) ⟨fun _ => 1, ?_, ?_, h0_dom, ?_, rfl⟩).trans ?_
          · intro _ _; norm_num
          · simp
          · intro v; exact IsEmpty.elim ‹IsEmpty V› v
          · simp [hg_zero]
        · have hle := lovasz_le_convexClosureVal rho hrho x
          dsimp [g] at hle
          rw [hlov_zero x] at hle
          exact hle
      rw [hcc_zero]
      simp [PosScalarMul]
  · intro p
    change ∃ k : ℤ, LovaszExtension rho (fun v => (p v : ℝ)) = ((k : ℝ) : WithTop ℝ)
    rw [← lovaszList_sortedValues]
    refine lovaszList_isIntegerValued rho hint (fun v => (p v : ℝ)) (SortedValues _) ?_
    intro a ha
    unfold SortedValues at ha
    rw [Finset.mem_sort, Finset.mem_image] at ha
    rcases ha with ⟨v, _, rfl⟩
    exact ⟨p v, rfl⟩
