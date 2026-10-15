-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-14T11:24:09.010899+00:00
-- url     : https://prove2.me/submissions/ecfc4a67-f204-42d5-bcd2-b0b863fb80f8

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

set_option autoImplicit false

open SimpleGraph

-- Proof of CycleLengthsExp.ManyLengths.lemma_2_5 (Friedman–Krivelevich, Lemma 2.5,
-- first assertion) by a DFS-style induction on pairs (P, T), where P is a path from v
-- and T is a "finished" set with no edges to the outside of T ∪ V(P).
-- At each step either P extends (endpoint has a fresh neighbour), or the endpoint is
-- "finished" (moved from P into T). The measure 2*(|V|-|T|) + (|V|-|V(P)|) drops by 1
-- at every step. The process stops when |T| = k-1 (then expansion applied to
-- W = T ∪ {endpoint} forces |V(P)| ≥ ℓ+1) or when |V(P)| ≥ ℓ+1 directly.

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

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) (hV : k < Fintype.card V)
    (hW : ∀ W : Set V, W.ncard = k → ℓ ≤ (CycleLengthsExp.WellSpread.extNbhd G W).ncard)
    (v : V) (hv : k ≤ {w | G.Reachable v w}.ncard) :
    ∃ (w : V) (p : G.Walk v w), p.IsPath ∧ p.length = ℓ := by
  classical
  refine aux_cyclelengths_lemma25_key G k ℓ hk hℓ hW v hv
    (2 * Fintype.card V + (Fintype.card V - 1)) ∅ (Walk.nil : G.Walk v v) ?_ ?_ ?_ ?_ ?_
  · exact Walk.IsPath.nil
  · exact Finset.disjoint_empty_left _
  · intro y hy
    exact absurd hy (Finset.notMem_empty y)
  · simp
  · rw [Walk.support_nil]
    simp

namespace CycleLengthsExp.ManyLengths

theorem lemma_2_5 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) (hV : k < Fintype.card V)
    (hW : ∀ W : Set V, W.ncard = k → ℓ ≤ (CycleLengthsExp.WellSpread.extNbhd G W).ncard)
    (v : V) (hv : k ≤ {w | G.Reachable v w}.ncard) :
    ∃ (w : V) (p : G.Walk v w), p.IsPath ∧ p.length = ℓ :=
  solution G k ℓ hk hℓ hV hW v hv

end CycleLengthsExp.ManyLengths
