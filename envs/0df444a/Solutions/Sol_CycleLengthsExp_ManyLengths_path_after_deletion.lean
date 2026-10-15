-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.path_after_deletion
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-15T02:05:53.934581+00:00
-- url     : https://prove2.me/submissions/0f19c5f9-7bcf-4e50-a354-be6c9aa504e1

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

set_option autoImplicit false

open SimpleGraph

-- DFS aux lemma, copied verbatim from the ACCEPTED lemma_2_5 proof
-- (~/workspace/p2m_harness/lemma25_proof_20261014.lean, sub ecfc4a67).
-- Induction on pairs (P, T): P a path from v, T "finished" with no edges to the
-- outside of T ∪ V(P). Measure 2*(|V|-|T|) + (|V|-|V(P)|) drops by 1 each step.

theorem aux_cyclelengths_lemma25_key {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ)
    (hW : ∀ W : Set V, W.ncard = k → ℓ ≤ (CycleLengthsExp.WellSpread.extNbhd G W).ncard)
    (v : V) (hv : k ≤ {w | G.Reachable v w}.ncard) :
    ∀ M : ℕ, ∀ (T : Finset V) {x : V} (P : G.Walk v x),
      P.IsPath →
      Disjoint T P.support.toFinset →
      (∀ y ∈ T, ∀ z : V, G.Adj y z → z ∈ T ∨ z ∈ P.support) →
      T.card ≤ k - 1 →
      2 * (Fintype.card V - T.card) + (Fintype.card V - P.support.toFinset.card) = M →
      ∃ w : V, ∃ p : G.Walk v w, p.IsPath ∧ p.length = ℓ := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M IH =>
    intro T x P hPath hDisj hClosed hTcard hM
    have hNodup : P.support.Nodup := (Walk.isPath_def P).mp hPath
    have hSupLen : P.support.length = P.length + 1 := Walk.length_support P
    have hScard : P.support.toFinset.card = P.length + 1 := by
      rw [List.toFinset_card_of_nodup hNodup, hSupLen]
    have hScard_le : P.support.toFinset.card ≤ Fintype.card V :=
      Finset.card_le_univ _
    have hx_mem : x ∈ P.support := Walk.end_mem_support P
    have hxS : x ∈ P.support.toFinset := List.mem_toFinset.mpr hx_mem
    have hxT : x ∉ T := Finset.disjoint_right.mp hDisj hxS
    have ncard_coe : ∀ (s : Finset V), (↑s : Set V).ncard = s.card := by
      intro s
      show ENat.toNat (↑s : Set V).encard = s.card
      rw [Set.encard_coe_eq_coe_finsetCard]
      simp
    by_cases hLen : ℓ ≤ P.length
    · -- Prefix of length ℓ.
      refine ⟨P.getVert ℓ, P.take ℓ, hPath.take ℓ, ?_⟩
      rw [Walk.take_length]
      exact Nat.min_eq_left hLen
    · have hLen' : P.length < ℓ := Nat.not_le.mp hLen
      by_cases hExt : ∃ y : V, G.Adj x y ∧ y ∉ T ∧ y ∉ P.support
      · -- Extend the path by one fresh edge.
        obtain ⟨y, hAdj, hyT, hyS⟩ := hExt
        have hyS' : y ∉ P.support.toFinset :=
          fun h => hyS (List.mem_toFinset.mp h)
        have hSup' : (P.concat hAdj).support = P.support ++ [y] :=
          Walk.support_concat P hAdj
        have hNodup' : (P.support ++ [y]).Nodup := by
          rw [List.nodup_append]
          refine ⟨hNodup, (List.nodup_cons).mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton] at hb
          rw [hb]
          intro h
          rw [h] at ha
          exact hyS ha
        have hScard' : (P.concat hAdj).support.toFinset.card =
            P.support.toFinset.card + 1 := by
          rw [hSup', List.toFinset_card_of_nodup hNodup', List.length_append,
            List.length_singleton, hSupLen, hScard]
        have hle : P.support.toFinset.card + 1 ≤ Fintype.card V := by
          have h1 := Finset.card_le_univ (insert y P.support.toFinset)
          rw [Finset.card_insert_of_notMem hyS'] at h1
          exact h1
        have hDisj' : Disjoint T (P.concat hAdj).support.toFinset := by
          rw [Finset.disjoint_left]
          intro a haT haSup
          rw [hSup', List.mem_toFinset, List.mem_append] at haSup
          rcases haSup with h | h
          · exact (Finset.disjoint_left.mp hDisj haT) (List.mem_toFinset.mpr h)
          · rw [List.mem_singleton] at h
            exact hyT (by rw [h] at haT; exact haT)
        have hClosed' : ∀ y' ∈ T, ∀ z : V, G.Adj y' z →
            z ∈ T ∨ z ∈ (P.concat hAdj).support := by
          intro y' hy' z hz
          rcases hClosed y' hy' z hz with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [hSup']; exact List.mem_append_left _ h)
        have hM' : 2 * (Fintype.card V - T.card) +
            (Fintype.card V - (P.concat hAdj).support.toFinset.card) = M - 1 := by
          omega
        exact IH (M - 1) (by omega) T (P.concat hAdj)
          (hPath.concat hyS hAdj) hDisj' hClosed' hTcard hM'
      · -- Endpoint has no fresh neighbour.
        have hN : ∀ y : V, G.Adj x y → y ∈ T ∨ y ∈ P.support := by
          intro y hy
          by_contra hcon
          apply hExt
          refine ⟨y, hy, ?_, ?_⟩
          · intro hyT; exact hcon (Or.inl hyT)
          · intro hyS; exact hcon (Or.inr hyS)
        by_cases hTk : T.card = k - 1
        · -- Stopping point: expansion on W = T ∪ {x} forces |V(P)| ≥ ℓ + 1.
          exfalso
          have hWcard : (insert x T).card = k := by
            rw [Finset.card_insert_of_notMem hxT]
            omega
          have hWncard : (↑(insert x T) : Set V).ncard = k := by
            rw [ncard_coe]
            exact hWcard
          have hExp := hW (↑(insert x T) : Set V) hWncard
          have hSub2 : CycleLengthsExp.WellSpread.extNbhd G (↑(insert x T) : Set V) ⊆
              ↑(P.support.toFinset.erase x) := by
            intro z hz
            obtain ⟨hzW, u, huW, huz⟩ := hz
            rw [Finset.mem_coe, Finset.mem_insert] at huW
            rw [Finset.mem_coe, Finset.mem_erase]
            refine ⟨fun hzx => hzW (by rw [Finset.mem_coe, hzx]; exact Finset.mem_insert_self x T), ?_⟩
            rcases huW with rfl | huT
            · rcases hN z huz with h | h
              · exfalso
                exact hzW (Finset.mem_coe.mpr (Finset.mem_insert_of_mem h))
              · exact List.mem_toFinset.mpr h
            · rcases hClosed u huT z huz with h | h
              · exfalso
                exact hzW (Finset.mem_coe.mpr (Finset.mem_insert_of_mem h))
              · exact List.mem_toFinset.mpr h
          have hle2 : (CycleLengthsExp.WellSpread.extNbhd G
              (↑(insert x T) : Set V)).ncard ≤
              (P.support.toFinset.erase x).card := by
            have h := Set.ncard_le_ncard hSub2 (Finset.finite_toSet _)
            rwa [ncard_coe] at h
          have hErase : (P.support.toFinset.erase x).card =
              P.support.toFinset.card - 1 :=
            Finset.card_erase_of_mem hxS
          omega
        · -- |T| < k - 1: finish the endpoint (move it from P into T).
          have hTlt : T.card + 1 < k := by omega
          by_cases hP0 : P.length = 0
          · -- P = [v] and T ∪ {v} is closed, so the component of v is inside
            -- T ∪ {v}, contradicting |component| ≥ k.
            exfalso
            have hxv : x = v := by
              have h1 : P.getVert P.length = x := Walk.getVert_length P
              rw [hP0, Walk.getVert_zero] at h1
              exact h1.symm
            have hvT : v ∉ T := by
              rw [← hxv]
              exact hxT
            have hsup : P.support = [v] := by
              have h1 : P.support.length = 1 := by rw [Walk.length_support, hP0]
              obtain ⟨a, ha⟩ : ∃ a, P.support = [a] := List.length_eq_one_iff.mp h1
              have h2 : v ∈ P.support := Walk.start_mem_support P
              rw [ha] at h2
              rw [List.mem_singleton] at h2
              rw [ha, h2]
            have hCclosed : ∀ y ∈ (↑(insert v T) : Set V), ∀ z : V, G.Adj y z →
                z ∈ (↑(insert v T) : Set V) := by
              intro y hy z hyz
              rw [Finset.mem_coe, Finset.mem_insert] at hy
              rcases hy with hyv | hyT
              · rw [hyv] at hyz
                rw [← hxv] at hyz
                rcases hN z hyz with h | h
                · rw [Finset.mem_coe, Finset.mem_insert]
                  exact Or.inr h
                · rw [hsup] at h
                  rw [List.mem_singleton] at h
                  rw [Finset.mem_coe, Finset.mem_insert]
                  exact Or.inl h
              · rcases hClosed y hyT z hyz with h | h
                · rw [Finset.mem_coe, Finset.mem_insert]
                  exact Or.inr h
                · rw [hsup] at h
                  rw [List.mem_singleton] at h
                  rw [Finset.mem_coe, Finset.mem_insert]
                  exact Or.inl h
            have hcomp : ∀ {a b : V} (p : G.Walk a b),
                a ∈ (↑(insert v T) : Set V) → b ∈ (↑(insert v T) : Set V) := by
              intro a b p
              induction p with
              | nil => intro ha; exact ha
              | cons h q ih => intro ha; exact ih (hCclosed _ ha _ h)
            have hsub : {w | G.Reachable v w} ⊆ ↑(insert v T) := by
              intro w hw
              obtain ⟨p⟩ := hw
              exact hcomp p (by rw [Finset.mem_coe]; exact Finset.mem_insert_self v T)
            have hle3 : {w | G.Reachable v w}.ncard ≤ (insert v T).card := by
              have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
              rwa [ncard_coe] at h
            have hcardT : (insert v T).card = T.card + 1 := by
              rw [Finset.card_insert_of_notMem hvT]
            omega
          · -- Drop the last vertex of P, move it into T.
            have hP1 : 1 ≤ P.length := Nat.one_le_iff_ne_zero.mpr hP0
            have htake : (P.take (P.length - 1)).support = P.support.take P.length := by
              rw [Walk.support_take,
                show P.length - 1 + 1 = P.length by omega]
            have hdrop : P.support.dropLast = P.support.take P.length := by
              rw [List.dropLast_eq_take,
                show P.support.length - 1 = P.length by rw [hSupLen]; omega]
            have hx_eq : x = P.support[P.length]'(by rw [hSupLen]; omega) := by
              have h1 := Walk.getVert_eq_support_getElem P (le_refl P.length)
              rwa [Walk.getVert_length] at h1
            have hne : P.support ≠ [] := List.ne_nil_of_mem hx_mem
            have hgetLast : P.support.getLast hne = x := by
              rw [List.getLast_eq_getElem hne]
              convert hx_eq.symm using 2
              omega
            have hx_not : x ∉ P.support.dropLast := by
              intro h
              have hnd : (P.support.dropLast ++ [P.support.getLast hne]).Nodup := by
                rw [List.dropLast_append_getLast hne]
                exact hNodup
              rw [List.nodup_append] at hnd
              have hne2 := hnd.2.2 x h (P.support.getLast hne)
                (List.mem_singleton_self _)
              rw [hgetLast] at hne2
              exact hne2 rfl
            have hmem_take : ∀ z ∈ P.support, z ≠ x →
                z ∈ (P.take (P.length - 1)).support := by
              intro z hz hzx
              rw [htake, ← hdrop]
              have hne2 : z ≠ P.support.getLast (List.ne_nil_of_mem hz) := by
                have hgl : P.support.getLast (List.ne_nil_of_mem hz) = x := hgetLast
                rw [hgl]
                exact hzx
              exact List.mem_dropLast_of_mem_of_ne_getLast hz hne2
            have hPath' : (P.take (P.length - 1)).IsPath := hPath.take _
            have hDisj' : Disjoint (insert x T)
                (P.take (P.length - 1)).support.toFinset := by
              rw [Finset.disjoint_left]
              intro a ha haSup
              rw [Finset.mem_insert] at ha
              rw [htake, List.mem_toFinset, ← hdrop] at haSup
              rcases ha with rfl | haT
              · exact hx_not haSup
              · have haS : a ∈ P.support.toFinset :=
                  List.mem_toFinset.mpr (List.mem_of_mem_dropLast haSup)
                exact (Finset.disjoint_right.mp hDisj haS) haT
            have hClosed' : ∀ y ∈ insert x T, ∀ z : V, G.Adj y z →
                z ∈ insert x T ∨ z ∈ (P.take (P.length - 1)).support := by
              intro y hy z hyz
              rw [Finset.mem_insert] at hy
              rcases hy with hyx | hyT
              · rw [hyx] at hyz
                rcases hN z hyz with h | h
                · exact Or.inl (Finset.mem_insert_of_mem h)
                · by_cases hzx : z = x
                  · exact Or.inl (by rw [Finset.mem_insert]; exact Or.inl hzx)
                  · exact Or.inr (hmem_take z h hzx)
              · rcases hClosed y hyT z hyz with h | h
                · exact Or.inl (Finset.mem_insert_of_mem h)
                · by_cases hzx : z = x
                  · exact Or.inl (by rw [Finset.mem_insert]; exact Or.inl hzx)
                  · exact Or.inr (hmem_take z h hzx)
            have hTcard' : (insert x T).card ≤ k - 1 := by
              rw [Finset.card_insert_of_notMem hxT]
              omega
            have hcardP' : (P.take (P.length - 1)).support.toFinset.card =
                P.support.toFinset.card - 1 := by
              rw [htake,
                List.toFinset_card_of_nodup
                  (List.Nodup.sublist (List.take_sublist _ _) hNodup),
                List.length_take, hSupLen, hScard]
              rw [Nat.min_eq_left (by omega : P.length ≤ P.length + 1)]
              omega
            have hM' : 2 * (Fintype.card V - (insert x T).card) +
                (Fintype.card V - (P.take (P.length - 1)).support.toFinset.card) =
                M - 1 := by
              have hcardT' : (insert x T).card = T.card + 1 :=
                Finset.card_insert_of_notMem hxT
              have hle1 : T.card + 1 ≤ Fintype.card V := by
                have h1 := Finset.card_le_univ (insert x T)
                rw [hcardT'] at h1
                exact h1
              have hle2 : P.support.toFinset.card - 1 ≤ Fintype.card V :=
                le_trans (Nat.sub_le _ _) hScard_le
              omega
            exact IH (M - 1) (by omega) (insert x T) (P.take (P.length - 1))
              hPath' hDisj' hClosed' hTcard' hM'

-- Main proof of path_after_deletion.
-- Strategy: run the DFS aux lemma on the induced subgraph G' = G.induce Sᶜ with
-- k = ⌈(L + |S|) / α⌉, L = ⌈αn/4⌉ - 1. Two facts carry the argument:
-- (1) extNbhd in G' loses at most |S| vs G: for W ⊆ Sᶜ, |N_{G'}(W)| ≥ α|W| - |S|,
--     so with αk ≥ L + |S| the aux hypothesis holds;
-- (2) some vertex of G' has reachable set ≥ k: otherwise a maximal union of
--     G'-components of size ≤ n/4 (each component has size ≤ |S|/α ≤ n/4 by
--     expansion, since its G-neighbours lie in S) could be enlarged past n/4
--     while staying ≤ n/2, contradicting expansion again.

theorem solution (n : ℕ) (hn : 0 < n) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) (S : Set (Fin n))
    (hS : S.ncard = Nat.floor (α * (n : ℝ) / 4)) :
    ∃ (u v : Fin n) (p : G.Walk u v),
      p.IsPath ∧ p.length = Nat.ceil (α * (n : ℝ) / 4) - 1 ∧
      ∀ w ∈ p.support, w ∉ S := by
  classical
  set G' := G.induce Sᶜ with hG'def
  set s : ℕ := S.ncard with hs_def
  set L : ℕ := Nat.ceil (α * (n : ℝ) / 4) - 1 with hL_def
  have hs_le : (s : ℝ) ≤ α * (n : ℝ) / 4 := by
    rw [hS]
    exact Nat.floor_le (by positivity)
  have hs_le_n4 : (s : ℝ) ≤ (n : ℝ) / 4 := by
    have h2 : α * (n : ℝ) ≤ (n : ℝ) := by
      have h3 := mul_le_mul_of_nonneg_right hα1 (show (0 : ℝ) ≤ (n : ℝ) by positivity)
      simpa using h3
    have h4 : α * (n : ℝ) / 4 ≤ (n : ℝ) / 4 := by linarith [h2]
    linarith
  have hs_n : s ≤ n := by
    have h1 : S.ncard ≤ (Set.univ : Set (Fin n)).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    rw [hs_def]
    exact h1
  have hcardSc : Fintype.card ↥Sᶜ = n - s := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_compl,
      Nat.card_eq_fintype_card, Fintype.card_fin, ← hs_def]
  have hceil_pos : 1 ≤ Nat.ceil (α * (n : ℝ) / 4) :=
    Nat.ceil_pos.mpr (by positivity)
  have hL_real : (L : ℝ) = (Nat.ceil (α * (n : ℝ) / 4) : ℝ) - 1 := by
    rw [hL_def, Nat.cast_sub hceil_pos]
    norm_num
  have hL_lt : (L : ℝ) < α * (n : ℝ) / 4 := by
    rw [hL_real]
    have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ α * (n : ℝ) / 4 by positivity)
    linarith
  have hExp : ∀ U : Set (Fin n), U.ncard ≤ (n + 1) / 2 →
      α * (U.ncard : ℝ) ≤
        ((CycleLengthsExp.WellSpread.extNbhd G U).ncard : ℝ) := by
    intro U hU
    exact hG U (by rw [Fintype.card_fin]; exact hU)
  -- Finset ncard helper (as in the lemma_2_5 proof).
  have ncard_coe : ∀ (t : Finset ↥Sᶜ), (↑t : Set ↥Sᶜ).ncard = t.card := by
    intro t
    show ENat.toNat (↑t : Set ↥Sᶜ).encard = t.card
    rw [Set.encard_coe_eq_coe_finsetCard]
    simp
  have ncard_image_val : ∀ (t : Finset ↥Sᶜ),
      ((fun x : ↥Sᶜ => (x : Fin n)) '' ↑t).ncard = t.card := by
    intro t
    rw [Set.ncard_image_of_injective _
      (Subtype.val_injective : Function.Injective (fun x : ↥Sᶜ => (x : Fin n))),
      ncard_coe]
  by_cases hL0 : L = 0
  · -- Length-0 path: any vertex outside S.
    obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
      by_contra hcon
      push_neg at hcon
      have hSeq : S = Set.univ := Set.eq_univ_of_forall hcon
      have hsn : s = n := by
        rw [hs_def, hSeq, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
      have h1 : (n : ℝ) ≤ (n : ℝ) / 4 := by
        have h2 : (s : ℝ) = (n : ℝ) := by exact_mod_cast hsn
        linarith [hs_le_n4]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    refine ⟨w, w, Walk.nil, Walk.IsPath.nil, ?_, ?_⟩
    · simp [hL0]
    · intro x hx
      rw [Walk.support_nil, List.mem_singleton] at hx
      rw [hx]
      exact hw
  · have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hL0
    set k : ℕ := Nat.ceil (((L : ℝ) + (s : ℝ)) / α) with hk_def
    have hk_pos : 0 < k := by
      rw [hk_def]
      apply Nat.ceil_pos.mpr
      have h1 : (0 : ℝ) < (L : ℝ) + (s : ℝ) := by
        have h2 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
        have h3 : (0 : ℝ) ≤ (s : ℝ) := by positivity
        linarith
      exact div_pos h1 hα
    have hk_ge : (L : ℝ) + (s : ℝ) ≤ α * (k : ℝ) := by
      have h1 : ((L : ℝ) + (s : ℝ)) / α ≤ (k : ℝ) := by
        rw [hk_def]
        exact Nat.le_ceil _
      have h2 : (L : ℝ) + (s : ℝ) ≤ (k : ℝ) * α := (div_le_iff₀ hα).mp h1
      linarith [h2]
    have hk_le_half : k ≤ (n + 1) / 2 := by
      rw [hk_def]
      apply Nat.ceil_le.mpr
      have h1 : ((L : ℝ) + (s : ℝ)) / α < (n : ℝ) / 2 := by
        have h2 : (L : ℝ) + (s : ℝ) < α * (n : ℝ) / 2 := by
          have h3 : (L : ℝ) + (s : ℝ) < α * (n : ℝ) / 4 + α * (n : ℝ) / 4 := by
            linarith [hL_lt, hs_le]
          linarith [h3]
        have h2' : (L : ℝ) + (s : ℝ) < (n : ℝ) / 2 * α := by
          rw [mul_comm ((n : ℝ) / 2) α, ← mul_div_assoc]
          exact h2
        exact (div_lt_iff₀ hα).mpr h2'
      have h3 : (n : ℝ) / 2 ≤ (((n + 1) / 2 : ℕ) : ℝ) := by
        have h4 : n ≤ 2 * ((n + 1) / 2) := by omega
        have h5 : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h4
        linarith
      linarith [h1, h3]
    -- Closed sets: G-neighbours of the image of a reachability-closed U lie in S.
    have hExt : ∀ U : Finset ↥Sᶜ, (∀ u ∈ U, ∀ x, G'.Reachable u x → x ∈ U) →
        CycleLengthsExp.WellSpread.extNbhd G ((fun x : ↥Sᶜ => (x : Fin n)) '' ↑U) ⊆ S := by
      intro U hU z hz
      obtain ⟨hzU, u, hu, hAdj⟩ := hz
      by_contra hzS
      obtain ⟨c, hcU, hcu⟩ := hu
      rw [← hcu] at hAdj
      have hAdj' : G'.Adj c ⟨z, hzS⟩ := hAdj
      have hreach : G'.Reachable c ⟨z, hzS⟩ := hAdj'.reachable
      have hcU' : c ∈ U := hcU
      have hzmem : (⟨z, hzS⟩ : ↥Sᶜ) ∈ U := hU c hcU' _ hreach
      exact hzU ⟨⟨z, hzS⟩, hzmem, rfl⟩
    -- Some vertex of G' has reachable set of size ≥ k.
    have hComp : ∃ v : ↥Sᶜ, k ≤ {w | G'.Reachable v w}.ncard := by
      by_contra hcon
      push_neg at hcon
      set 𝒜 : Finset (Finset ↥Sᶜ) := Finset.univ.powerset.filter
        (fun A => (∀ u ∈ A, ∀ x, G'.Reachable u x → x ∈ A) ∧ (A.card : ℝ) ≤ (n : ℝ) / 4)
        with h𝒜def
      have hne : 𝒜.Nonempty := by
        refine ⟨∅, ?_⟩
        rw [h𝒜def, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.subset_univ _, ?_, ?_⟩
        · intro u hu
          exact absurd hu (Finset.notMem_empty u)
        · rw [Finset.card_empty, Nat.cast_zero]
          positivity
      obtain ⟨A, hAmem, hAmax⟩ := Finset.exists_max_image 𝒜 Finset.card hne
      rw [h𝒜def, Finset.mem_filter, Finset.mem_powerset] at hAmem
      obtain ⟨hAsub, hAclosed, hAsmall⟩ := hAmem
      by_cases hAuniv : A = Finset.univ
      · have h1 : A.card = Fintype.card ↥Sᶜ := by rw [hAuniv, Finset.card_univ]
        rw [hcardSc] at h1
        have h2 : ((n - s : ℕ) : ℝ) = (n : ℝ) - (s : ℝ) := Nat.cast_sub hs_n
        have h3 : (A.card : ℝ) = (n : ℝ) - (s : ℝ) := by rw [h1]; exact h2
        have hn1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        linarith [hAsmall, hs_le_n4, hn1, h3]
      · obtain ⟨w, hw⟩ : ∃ w, w ∉ A := by
          by_contra hcon2
          push_neg at hcon2
          exact hAuniv (Finset.eq_univ_of_forall hcon2)
        set C : Finset ↥Sᶜ := Finset.univ.filter (fun x => G'.Reachable w x) with hCdef
        have hwC : w ∈ C := by
          rw [hCdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩
        have hCclosed : ∀ u ∈ C, ∀ x, G'.Reachable u x → x ∈ C := by
          intro u hu x hux
          rw [hCdef, Finset.mem_filter] at hu ⊢
          exact ⟨Finset.mem_univ _, (hu.2).trans hux⟩
        have hdisj : Disjoint C A := by
          rw [Finset.disjoint_left]
          intro x hxC hxA
          rw [hCdef, Finset.mem_filter] at hxC
          have hwa : w ∈ A := hAclosed x hxA w hxC.2.symm
          exact hw hwa
        by_cases hkC : k ≤ C.card
        · have h1 : {x | G'.Reachable w x} = (↑C : Set ↥Sᶜ) := by
            ext x
            simp [hCdef]
          have h2 : {x | G'.Reachable w x}.ncard = C.card := by
            rw [h1, ncard_coe]
          have hcw := hcon w
          rw [h2] at hcw
          omega
        · have hCk : C.card < k := Nat.not_le.mp hkC
          set C₀ : Set (Fin n) := (fun x : ↥Sᶜ => (x : Fin n)) '' ↑C with hC₀def
          have hC₀ncard : C₀.ncard = C.card := by
            rw [hC₀def, ncard_image_val]
          have hC₀le : C₀.ncard ≤ (n + 1) / 2 := by
            rw [hC₀ncard]
            omega
          have hexpC : α * (C.card : ℝ) ≤
              (CycleLengthsExp.WellSpread.extNbhd G C₀).ncard := by
            have h := hExp C₀ hC₀le
            rw [hC₀ncard] at h
            exact h
          have hsubC : CycleLengthsExp.WellSpread.extNbhd G C₀ ⊆ S := hExt C hCclosed
          have hleC : (CycleLengthsExp.WellSpread.extNbhd G C₀).ncard ≤ s := by
            have h1 := Set.ncard_le_ncard hsubC (Set.toFinite S)
            rw [hs_def]
            exact h1
          have hCsmall : (C.card : ℝ) ≤ (n : ℝ) / 4 := by
            have h1 : ((CycleLengthsExp.WellSpread.extNbhd G C₀).ncard : ℝ) ≤
                α * ((n : ℝ) / 4) := by
              have h2 : ((CycleLengthsExp.WellSpread.extNbhd G C₀).ncard : ℝ) ≤
                  (s : ℝ) := by exact_mod_cast hleC
              linarith [h2, hs_le]
            have h3 : α * (C.card : ℝ) ≤ α * ((n : ℝ) / 4) := le_trans hexpC h1
            exact le_of_mul_le_mul_left h3 hα
          have hACclosed : ∀ u ∈ A ∪ C, ∀ x, G'.Reachable u x → x ∈ A ∪ C := by
            intro u hu x hux
            rw [Finset.mem_union] at hu ⊢
            rcases hu with hu | hu
            · exact Or.inl (hAclosed u hu x hux)
            · exact Or.inr (hCclosed u hu x hux)
          have hcardAC : (A ∪ C).card = A.card + C.card :=
            Finset.card_union_of_disjoint hdisj.symm
          have hACgt : (n : ℝ) / 4 < ((A ∪ C).card : ℝ) := by
            by_contra hcon3
            push_neg at hcon3
            have hmem : A ∪ C ∈ 𝒜 := by
              rw [h𝒜def, Finset.mem_filter, Finset.mem_powerset]
              exact ⟨Finset.subset_univ _, hACclosed, hcon3⟩
            have hlt := hAmax (A ∪ C) hmem
            have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨w, hwC⟩
            omega
          set U₀ : Set (Fin n) := (fun x : ↥Sᶜ => (x : Fin n)) '' ↑(A ∪ C) with hU₀def
          have hU₀ncard : U₀.ncard = (A ∪ C).card := by
            rw [hU₀def, ncard_image_val]
          have hU₀le : U₀.ncard ≤ (n + 1) / 2 := by
            have h1 : (U₀.ncard : ℝ) ≤ (n : ℝ) / 2 := by
              rw [hU₀ncard]
              have h2 : ((A ∪ C).card : ℝ) = (A.card : ℝ) + (C.card : ℝ) := by
                exact_mod_cast hcardAC
              linarith [hAsmall, hCsmall, h2]
            have h2 : (n : ℝ) / 2 ≤ (((n + 1) / 2 : ℕ) : ℝ) := by
              have h3 : n ≤ 2 * ((n + 1) / 2) := by omega
              have h4 : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h3
              linarith
            have h3 : (U₀.ncard : ℝ) ≤ (((n + 1) / 2 : ℕ) : ℝ) := le_trans h1 h2
            exact_mod_cast h3
          have hexpU : α * (U₀.ncard : ℝ) ≤
              (CycleLengthsExp.WellSpread.extNbhd G U₀).ncard := hExp U₀ hU₀le
          have hsubU : CycleLengthsExp.WellSpread.extNbhd G U₀ ⊆ S :=
            hExt (A ∪ C) hACclosed
          have hleU : (CycleLengthsExp.WellSpread.extNbhd G U₀).ncard ≤ s := by
            have h1 := Set.ncard_le_ncard hsubU (Set.toFinite S)
            rw [hs_def]
            exact h1
          have hU₀small : (U₀.ncard : ℝ) ≤ (n : ℝ) / 4 := by
            have h1 : ((CycleLengthsExp.WellSpread.extNbhd G U₀).ncard : ℝ) ≤
                α * ((n : ℝ) / 4) := by
              have h2 : ((CycleLengthsExp.WellSpread.extNbhd G U₀).ncard : ℝ) ≤
                  (s : ℝ) := by exact_mod_cast hleU
              linarith [h2, hs_le]
            have h3 : α * (U₀.ncard : ℝ) ≤ α * ((n : ℝ) / 4) := le_trans hexpU h1
            exact le_of_mul_le_mul_left h3 hα
          have h4 : (U₀.ncard : ℝ) = ((A ∪ C).card : ℝ) := by rw [hU₀ncard]
          linarith [hU₀small, hACgt, h4]
    -- Expansion for the aux lemma: extNbhd in G' loses at most |S|.
    have hW : ∀ W : Set ↥Sᶜ, W.ncard = k →
        L ≤ (CycleLengthsExp.WellSpread.extNbhd G' W).ncard := by
      intro W hWk
      set W₀ : Set (Fin n) := (fun x : ↥Sᶜ => (x : Fin n)) '' W with hW₀def
      have hW₀ncard : W₀.ncard = k := by
        rw [hW₀def, Set.ncard_image_of_injective _
          (Subtype.val_injective : Function.Injective (fun x : ↥Sᶜ => (x : Fin n))), hWk]
      have hW₀le : W₀.ncard ≤ (n + 1) / 2 := by
        rw [hW₀ncard]
        exact hk_le_half
      have hexpW : α * (k : ℝ) ≤
          (CycleLengthsExp.WellSpread.extNbhd G W₀).ncard := by
        have h := hExp W₀ hW₀le
        rw [hW₀ncard] at h
        exact h
      have hsub : CycleLengthsExp.WellSpread.extNbhd G W₀ \ S ⊆
          (fun x : ↥Sᶜ => (x : Fin n)) ''
            (CycleLengthsExp.WellSpread.extNbhd G' W) := by
        intro z hz
        obtain ⟨hzW₀, hzS⟩ := hz
        obtain ⟨hzW₀', u, hu, hAdj⟩ := hzW₀
        obtain ⟨c, hcW, hcu⟩ := hu
        refine ⟨⟨z, hzS⟩, ?_, rfl⟩
        refine ⟨?_, c, hcW, ?_⟩
        · intro hmem
          exact hzW₀' ⟨⟨z, hzS⟩, hmem, rfl⟩
        · rw [← hcu] at hAdj
          exact hAdj
      have hle1 : (CycleLengthsExp.WellSpread.extNbhd G W₀ \ S).ncard ≤
          (CycleLengthsExp.WellSpread.extNbhd G' W).ncard := by
        have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
        have h2 : ((fun x : ↥Sᶜ => (x : Fin n)) ''
            (CycleLengthsExp.WellSpread.extNbhd G' W)).ncard =
            (CycleLengthsExp.WellSpread.extNbhd G' W).ncard :=
          Set.ncard_image_of_injective _
            (Subtype.val_injective : Function.Injective (fun x : ↥Sᶜ => (x : Fin n)))
        rw [h2] at h1
        exact h1
      have hle2 : (CycleLengthsExp.WellSpread.extNbhd G W₀).ncard ≤
          (CycleLengthsExp.WellSpread.extNbhd G W₀ \ S).ncard + s := by
        have h1 : CycleLengthsExp.WellSpread.extNbhd G W₀ ⊆
            (CycleLengthsExp.WellSpread.extNbhd G W₀ \ S) ∪ S := by
          intro z hz
          by_cases hzS : z ∈ S
          · exact Or.inr hzS
          · exact Or.inl ⟨hz, hzS⟩
        have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
        have h3 := Set.ncard_union_le
          (CycleLengthsExp.WellSpread.extNbhd G W₀ \ S) S
        rw [hs_def]
        omega
      have hchain : (L : ℝ) ≤
          ((CycleLengthsExp.WellSpread.extNbhd G' W).ncard : ℝ) := by
        have h1 : ((CycleLengthsExp.WellSpread.extNbhd G W₀).ncard : ℝ) ≤
            ((CycleLengthsExp.WellSpread.extNbhd G W₀ \ S).ncard : ℝ) + (s : ℝ) := by
          exact_mod_cast hle2
        have h2 : ((CycleLengthsExp.WellSpread.extNbhd G W₀ \ S).ncard : ℝ) ≤
            ((CycleLengthsExp.WellSpread.extNbhd G' W).ncard : ℝ) := by
          exact_mod_cast hle1
        linarith [hexpW, hk_ge, h1, h2]
      exact_mod_cast hchain
    obtain ⟨v, hv⟩ := hComp
    obtain ⟨w', p', hp'path, hp'len⟩ :=
      aux_cyclelengths_lemma25_key G' k L hk_pos hL1 hW v hv
        (2 * Fintype.card ↥Sᶜ + (Fintype.card ↥Sᶜ - 1)) ∅ (Walk.nil : G'.Walk v v)
        Walk.IsPath.nil (Finset.disjoint_empty_left _)
        (by intro y hy; exact absurd hy (Finset.notMem_empty y))
        (by simp)
        (by rw [Walk.support_nil]; simp)
    let f : G' →g G := ⟨Subtype.val, fun h => h⟩
    refine ⟨(v : Fin n), (w' : Fin n), p'.map f, ?_, ?_, ?_⟩
    · exact (SimpleGraph.Walk.isPath_map_iff_of_injective (f := f)
        (Subtype.val_injective : Function.Injective (fun x : ↥Sᶜ => (x : Fin n)))).mpr
        hp'path
    · rw [Walk.length_map, hp'len]
    · intro x hx
      rw [Walk.support_map, List.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hxy : x = (y : Fin n) := hyx.symm
      rw [hxy]
      exact y.2

namespace CycleLengthsExp.ManyLengths

theorem path_after_deletion (n : ℕ) (hn : 0 < n) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) (S : Set (Fin n))
    (hS : S.ncard = Nat.floor (α * (n : ℝ) / 4)) :
    ∃ (u v : Fin n) (p : G.Walk u v),
      p.IsPath ∧ p.length = Nat.ceil (α * (n : ℝ) / 4) - 1 ∧
      ∀ w ∈ p.support, w ∉ S :=
  solution n hn α hα hα1 G hG S hS

end CycleLengthsExp.ManyLengths
