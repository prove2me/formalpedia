-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.lovasz_extension_is_polyhedral_lconvex
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:20:23.199416+00:00
-- url     : https://prove2.me/submissions/7fa582b4-9608-47e3-8abe-25ff799b1219

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LovaszExtension
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsC

variable {V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def lovaszList (rho : Finset V → WithTop ℝ) (p : V → ℝ) : List ℝ → WithTop ℝ
  | [] => 0
  | [a] => PosScalarMul a (rho (Finset.univ.filter (fun v => a ≤ p v)))
  | a :: b :: rest =>
      PosScalarMul (a - b) (rho (Finset.univ.filter (fun v => a ≤ p v))) +
        lovaszList rho p (b :: rest)

private lemma posScalarMul_zero (x : WithTop ℝ) : PosScalarMul 0 x = 0 := by
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

private lemma pairwise_insLow (c : ℝ) : ∀ {L : List ℝ},
    List.Pairwise (· > ·) L → List.Pairwise (· > ·) (insLow c L)
  | [], _ => List.pairwise_singleton _ _
  | a :: rest, hpw => by
      rcases List.pairwise_cons.mp hpw with ⟨ha, hrest⟩
      simp only [insLow]
      split_ifs with h1 h2
      · exact hpw
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, hpw⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h2
        · exact lt_trans (ha x hx) h2
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, pairwise_insLow c hrest⟩
        rcases mem_insLow.mp hx with rfl | hx
        · exact lt_of_le_of_ne (not_lt.mp h2) h1
        · exact ha x hx

private lemma insLow_ne_nil (c : ℝ) (L : List ℝ) : insLow c L ≠ [] := by
  cases L with
  | nil => simp [insLow]
  | cons a rest =>
    simp only [insLow]
    split_ifs <;> simp

private lemma eq_of_pairwise_gt : ∀ {L₁ L₂ : List ℝ},
    List.Pairwise (· > ·) L₁ → List.Pairwise (· > ·) L₂ →
    (∀ x, x ∈ L₁ ↔ x ∈ L₂) → L₁ = L₂
  | [], [], _, _, _ => rfl
  | a :: L₁, [], _, _, hmem => False.elim ((List.not_mem_nil) ((hmem a).mp List.mem_cons_self))
  | [], b :: L₂, _, _, hmem => False.elim ((List.not_mem_nil) ((hmem b).mpr List.mem_cons_self))
  | a :: L₁, b :: L₂, hpw₁, hpw₂, hmem => by
      rcases List.pairwise_cons.mp hpw₁ with ⟨ha, hrest₁⟩
      rcases List.pairwise_cons.mp hpw₂ with ⟨hb, hrest₂⟩
      have hab : a = b := by
        have ha_in : a ∈ b :: L₂ := (hmem a).mp List.mem_cons_self
        have hb_in : b ∈ a :: L₁ := (hmem b).mpr List.mem_cons_self
        rcases List.mem_cons.mp ha_in with rfl | ha_in
        · rfl
        · rcases List.mem_cons.mp hb_in with rfl | hb_in
          · rfl
          · exact False.elim (lt_asymm (hb a ha_in) (ha b hb_in))
      subst hab
      congr 1
      refine eq_of_pairwise_gt hrest₁ hrest₂ (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
      · have hx' : x ∈ a :: L₂ := (hmem x).mp (List.mem_cons_of_mem a hx)
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact False.elim (lt_irrefl x (ha x hx))
        · exact hx'
      · have hx' : x ∈ a :: L₁ := (hmem x).mpr (List.mem_cons_of_mem a hx)
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact False.elim (lt_irrefl x (hb x hx))
        · exact hx'

private lemma pairwise_gt_sort (s : Finset ℝ) : List.Pairwise (· > ·) (s.sort (· ≥ ·)) := by
  have hle := Finset.pairwise_sort s (· ≥ ·)
  have hnd := Finset.sort_nodup s (· ≥ ·)
  rw [List.Nodup, List.pairwise_iff_getElem] at hnd
  rw [List.pairwise_iff_getElem] at hle ⊢
  intro i j hi hj hij
  exact lt_of_le_of_ne (hle i j hi hj hij) (Ne.symm (hnd i j hi hj hij))

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

private lemma sortedValues_ne_nil [Nonempty V] (p : V → ℝ) : SortedValues p ≠ [] := by
  classical
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

theorem solution (rho : Finset V → WithTop ℝ)
    (hrho : SubmodularSetFunction rho) :
    SBFR (LovaszExtension rho) ∧ TRFR (LovaszExtension rho) := by
  by_cases hV : Nonempty V
  · have : Nonempty V := hV
    refine ⟨fun p q => ?_, ?_⟩
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
  · have : IsEmpty V := not_nonempty_iff.mp hV
    have hsort_nil : ∀ p : V → ℝ, SortedValues p = [] := by
      intro p
      unfold SortedValues
      simp [Finset.univ_eq_empty]
    have hlov_zero : ∀ p : V → ℝ, LovaszExtension rho p = 0 := by
      intro p
      rw [← lovaszList_sortedValues, hsort_nil]
      rfl
    refine ⟨fun p q => by simp [hlov_zero], ⟨0, fun p alpha => by simp [hlov_zero]⟩⟩
