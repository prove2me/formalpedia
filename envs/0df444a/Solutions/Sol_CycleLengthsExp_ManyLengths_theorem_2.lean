-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-19T16:32:59.899693+00:00
-- url     : https://prove2.me/submissions/8c7f8aa2-73c1-42e7-8c03-0d16eb2f7c3d

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

set_option autoImplicit false

open SimpleGraph CycleLengthsExp CycleLengthsExp.ManyLengths


/-- Friedman–Krivelevich, Cycle lengths in expanding graphs, p. 13, proof of
Theorem 2: the explicitly chosen integer `k(α) = 2⌈log₂(3/α)/log₂(1+α/2)⌉+1`
satisfies `k(α) ≤ K * log₂(2/α)/α` for an absolute constant `K > 0`,
uniformly for `0 < α ≤ 1`.

Proof idea: `⌈x⌉ ≤ x+1`; `log₂(3/α) ≤ 2*log₂(2/α)` (as `3/α ≤ (2/α)²`
for `α ≤ 1`); `log₂(1+α/2) ≥ α/(3*log 2)` (from `log(1+t) ≥ t/(1+t)`);
absorbing the `+3` constant via `log₂(2/α)/α ≥ 1`. Witness:
`K = 12*log 2 + 3`.

`solution` is top-level (the verifier looks up unqualified `solution`);
`CycleLengthsExp.ManyLengths.k_bound` below is the ascribed alias matching
the published node name. -/
theorem k_bound_proof : ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    (kNum α : ℝ) ≤ K * Real.logb 2 (2 / α) / α := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨12 * Real.log 2 + 3, by linarith, fun α hα0 hα1 => ?_⟩
  have hαne : α ≠ 0 := ne_of_gt hα0
  have hlogne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  -- (i) L := logb 2 (2/α) ≥ 1
  have hL1 : (1:ℝ) ≤ Real.logb 2 (2 / α) := by
    have h2 : (2:ℝ) ≤ 2 / α := by
      rw [le_div_iff₀ hα0]
      linarith [hα1]
    calc (1:ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (2 / α) :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2
  -- (ii) numerator: logb 2 (3/α) ≤ 2 * logb 2 (2/α)
  have hnum : Real.logb 2 (3 / α) ≤ 2 * Real.logb 2 (2 / α) := by
    have h3α : (3:ℝ) / α ≤ (2 / α) ^ 2 := by
      have hαsq : (0:ℝ) < α ^ 2 := by positivity
      have e1 : (3:ℝ) / α = (3 * α) / (α ^ 2) := by
        field_simp
      have e2 : ((2:ℝ) / α) ^ 2 = 4 / (α ^ 2) := by
        field_simp
        ring
      rw [e1, e2, div_le_div_iff_of_pos_right hαsq]
      linarith [hα1]
    have h3αpos : (0:ℝ) < 3 / α := div_pos (by norm_num) hα0
    calc Real.logb 2 (3 / α) ≤ Real.logb 2 ((2 / α) ^ 2) :=
            Real.logb_le_logb_of_le (by norm_num) h3αpos h3α
      _ = 2 * Real.logb 2 (2 / α) := by
            simp only [Real.logb_pow, Nat.cast_ofNat]
  -- (iii) denominator: logb 2 (1+α/2) ≥ α / (3 * log 2)
  have hden : α / (3 * Real.log 2) ≤ Real.logb 2 (1 + α / 2) := by
    have hpos : (0:ℝ) < 1 + α / 2 := by linarith
    have h1ln : (α / 3 : ℝ) ≤ Real.log (1 + α / 2) := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
      rw [Real.log_inv] at h
      have h2 : (1:ℝ) - (1 + α / 2)⁻¹ ≤ Real.log (1 + α / 2) := by linarith
      have hne : ((1:ℝ) + α / 2) ≠ 0 := ne_of_gt hpos
      have e : (1:ℝ) - (1 + α / 2)⁻¹ = (α / 2) / (1 + α / 2) := by
        rw [inv_eq_one_div]
        field_simp
        ring
      have hα2 : α ^ 2 ≤ α := by
        have h := mul_le_mul_of_nonneg_left hα1 (le_of_lt hα0)
        rw [mul_one] at h
        have e2 : α ^ 2 = α * α := by ring
        rw [e2]; exact h
      have h3 : (α / 3 : ℝ) ≤ (α / 2) / (1 + α / 2) := by
        rw [le_div_iff₀ hpos]
        have e : (α / 3) * (1 + α / 2) = α / 2 - (α - α ^ 2) / 6 := by ring
        rw [e]
        have hnn : (0:ℝ) ≤ (α - α ^ 2) / 6 :=
          div_nonneg (by linarith [hα2]) (by norm_num)
        linarith
      rw [e] at h2
      exact h3.trans h2
    have hlogb_eq : Real.logb 2 (1 + α / 2)
        = Real.log (1 + α / 2) / Real.log 2 := rfl
    have h3' : (α / 3 : ℝ) / Real.log 2
        ≤ Real.log (1 + α / 2) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog2).mpr h1ln
    have eα : α / (3 * Real.log 2) = (α / 3) / Real.log 2 := by ring
    rw [hlogb_eq, eα]
    exact h3'
  have hdenpos : (0:ℝ) < Real.logb 2 (1 + α / 2) := by
    have hα3 : (0:ℝ) < α / (3 * Real.log 2) :=
      div_pos hα0 (mul_pos (by norm_num) hlog2)
    exact lt_of_lt_of_le hα3 hden
  -- (iv) the ratio A := logb 2 (3/α) / logb 2 (1+α/2) ≤ 6 * log 2 * L / α
  have hA : Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)
      ≤ 6 * Real.log 2 * Real.logb 2 (2 / α) / α := by
    rw [div_le_iff₀ hdenpos]
    have hnn : (0:ℝ) ≤ 6 * Real.log 2 * Real.logb 2 (2 / α) / α :=
      div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hlog2))
          (le_trans (by norm_num) hL1)) (le_of_lt hα0)
    have hmul := mul_le_mul_of_nonneg_left hden hnn
    have h3logne : (3:ℝ) * Real.log 2 ≠ 0 := mul_ne_zero (by norm_num) hlogne
    have eR : (6 * Real.log 2 * Real.logb 2 (2 / α) / α) * (α / (3 * Real.log 2))
        = 2 * Real.logb 2 (2 / α) := by
      field_simp
      ring
    rw [eR] at hmul
    calc Real.logb 2 (3 / α) ≤ 2 * Real.logb 2 (2 / α) := hnum
      _ ≤ (6 * Real.log 2 * Real.logb 2 (2 / α) / α)
          * Real.logb 2 (1 + α / 2) := hmul
  -- (v) ceil: ↑⌈A⌉₊ ≤ A + 1
  have hA0 : (0:ℝ) ≤ Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2) :=
    div_nonneg
      (Real.logb_nonneg (by norm_num) (by
        rw [le_div_iff₀ hα0]
        linarith [hα1]))
      (le_of_lt hdenpos)
  have hceil : ((Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) : ℕ) : ℝ)
      ≤ Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2) + 1 :=
    (Nat.ceil_lt_add_one hA0).le
  -- (vi) absorb the +3 via logb 2 (2/α) / α ≥ 1
  have hM : (1:ℝ) ≤ Real.logb 2 (2 / α) / α := by
    rw [le_div_iff₀ hα0]
    linarith [hL1, hα1]
  -- assembly
  unfold kNum
  push_cast
  have step1 : (2 * ((Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) : ℕ) : ℝ) + 1)
      ≤ 2 * (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 3 := by
    have h1 := mul_le_mul_of_nonneg_left hceil (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have step2 : (2 * (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 3)
      ≤ 2 * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3 := by
    have h2 := mul_le_mul_of_nonneg_left hA (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have step3 : (2 * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3)
      ≤ (12 * Real.log 2 + 3) * (Real.logb 2 (2 / α) / α) := by
    have h3M : (3:ℝ) ≤ 3 * (Real.logb 2 (2 / α) / α) := by linarith [hM]
    have e2 : (12 * Real.log 2 + 3) * (Real.logb 2 (2 / α) / α)
        = 12 * Real.log 2 * (Real.logb 2 (2 / α) / α)
          + 3 * (Real.logb 2 (2 / α) / α) := by ring
    rw [e2]
    have key : (2:ℝ) * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3
        ≤ 12 * Real.log 2 * (Real.logb 2 (2 / α) / α)
          + 3 * (Real.logb 2 (2 / α) / α) := by
      have ering : (2:ℝ) * (6 * Real.log 2 * Real.logb 2 (2 / α) / α)
          = 12 * Real.log 2 * (Real.logb 2 (2 / α) / α) := by ring
      rw [ering]
      have hle := add_le_add_right h3M
        (12 * Real.log 2 * (Real.logb 2 (2 / α) / α))
      linarith
    exact key
  calc (2 * ((Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) : ℕ) : ℝ) + 1)
        ≤ 2 * (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 3 := step1
      _ ≤ 2 * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3 := step2
      _ ≤ (12 * Real.log 2 + 3) * (Real.logb 2 (2 / α) / α) := step3
      _ = (12 * Real.log 2 + 3) * Real.logb 2 (2 / α) / α := by ring

-- Dual-named alias: the platform looks up `CycleLengthsExp.ManyLengths.k_bound`.

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

theorem lemma_2_5_proof {V : Type*} [Fintype V] (G : SimpleGraph V)
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

theorem path_after_deletion_proof (n : ℕ) (hn : 0 < n) (α : ℝ)
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


/-- Ball of radius `r` around `Seed` by walks. -/
@[reducible]
def walkBall {V : Type*} (G : SimpleGraph V) (Seed : Set V) (r : ℕ) : Set V :=
  {w | ∃ s ∈ Seed, ∃ q : G.Walk s w, q.length ≤ r}

/-- `dropLast` commutes with `map`. -/
theorem List.dropLast_map' {V W : Type*} (f : V → W) (l : List V) :
    (l.map f).dropLast = (l.dropLast).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l' =>
      simp [List.dropLast_cons_cons]

/-- `tail` commutes with `map`. -/
theorem List.tail_map' {V W : Type*} (f : V → W) (l : List V) :
    (l.map f).tail = (l.tail).map f := by
  cases l with
  | nil => rfl
  | cons a l => rfl

/-- `tail` + `dropLast` commute with `map`. -/
theorem List.tail_dropLast_map {V W : Type*} (f : V → W) (l : List V) :
    (l.map f).tail.dropLast = (l.tail.dropLast).map f := by
  rw [List.tail_map', List.dropLast_map']

/-- A vertex in the tail of a path's support is not the start vertex. -/
theorem walk_mem_tail_ne_start {V : Type*} {G : SimpleGraph V} {s y : V} {q : G.Walk s y}
    (hq : q.IsPath) {z : V} (hz : z ∈ q.support.tail) : z ≠ s := by
  cases q with
  | nil => simp at hz
  | cons h q' =>
    rw [Walk.support_cons, List.tail_cons] at hz
    have hnod : (Walk.cons h q').support.Nodup := (Walk.isPath_def _).mp hq
    rw [Walk.support_cons] at hnod
    exact fun hze => (List.nodup_cons.mp hnod).1 (hze ▸ hz)

/-- A vertex in the `dropLast` of a path's support is not the end vertex. -/
theorem walk_mem_dropLast_ne_end {V : Type*} {G : SimpleGraph V} {s y : V} {q : G.Walk s y}
    (hq : q.IsPath) {z : V} (hz : z ∈ q.support.dropLast) : z ≠ y := by
  intro hze
  have hne : q.support ≠ [] := q.support_ne_nil
  have hgetLast : q.support.getLast hne = y := by
    have h1 : q.support.length - 1 = q.length := by
      rw [Walk.length_support]
      omega
    have h2 : q.support[q.support.length - 1] = y := by
      have hlt : q.support.length - 1 ≤ q.length := by
        have hls := Walk.length_support q
        omega
      have hget : q.getVert (q.support.length - 1) = y := by
        rw [h1]
        exact Walk.getVert_length q
      exact (Walk.getVert_eq_support_getElem q hlt).symm.trans hget
    rw [List.getLast_eq_getElem]
    exact h2
  have h1 : q.support.dropLast ++ [q.support.getLast hne] = q.support :=
    List.dropLast_append_getLast hne
  have hnod : (q.support.dropLast ++ [q.support.getLast hne]).Nodup := by
    rw [List.dropLast_append_getLast]
    exact (Walk.isPath_def _).mp hq
  have h3 : z ≠ q.support.getLast hne :=
    (List.nodup_append.mp hnod).2.2 z hz _ (List.mem_singleton_self _)
  rw [hgetLast] at h3
  exact h3 hze

open CycleLengthsExp.ManyLengths in
theorem x0_large_proof (n : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hn : 12 ≤ α * (n : ℝ)) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) (S : Set (Fin n))
    (hS : S.ncard = Nat.floor (α * (n : ℝ) / 4))
    (u v : Fin n) (p : G.Walk u v) (hp : p.IsPath)
    (hlen : p.length = Nat.ceil (α * (n : ℝ) / 4) - 1)
    (hdisj : ∀ w ∈ p.support, w ∉ S) :
    α ^ 2 * (n : ℝ) / 12 ≤ ((X0 α G S p).ncard : ℝ) := by
  classical
  set X0 : Set (Fin n) := CycleLengthsExp.ManyLengths.X0 α G S p with hX0def
  set G' := G.induce X0ᶜ with hG'def
  set m : ℕ := Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) with hm_def
  set Pset : Set (Fin n) := ↑p.support.toFinset with hPsetdef
  set S' : Set ↥X0ᶜ := {w | (w : Fin n) ∈ S} with hS'def
  set P' : Set ↥X0ᶜ := {w | (w : Fin n) ∈ Pset} with hP'def
  -- Basic real facts.
  have hαn_pos : (0 : ℝ) < α * (n : ℝ) := by linarith
  have hαn_le : α * (n : ℝ) ≤ (n : ℝ) := by
    calc α * (n : ℝ) ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hα1 (by positivity)
      _ = (n : ℝ) := one_mul _
  have hnR : (12 : ℝ) ≤ (n : ℝ) := le_trans hn hαn_le
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hlog : (0 : ℝ) < Real.logb 2 (1 + α / 2) :=
    Real.logb_pos (by norm_num) (by linarith)
  -- `(1 + α/2)^m ≥ 3/α` from the definition of `m`.
  have hpow : (3 / α) ≤ (1 + α / 2) ^ m := by
    have h1 : Real.logb 2 (3 / α) ≤ (m : ℝ) * Real.logb 2 (1 + α / 2) := by
      have h2 : Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2) ≤ (m : ℝ) := by
        rw [hm_def]
        exact Nat.le_ceil _
      have h3 : Real.logb 2 (3 / α) =
          (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) *
            Real.logb 2 (1 + α / 2) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hlog)]
      rw [h3]
      exact mul_le_mul_of_nonneg_right h2 (le_of_lt hlog)
    have hle : Real.logb 2 (3 / α) ≤ Real.logb 2 ((1 + α / 2) ^ m) := by
      rw [Real.logb_pow]
      exact h1
    exact (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mp hle
  -- `|S| > αn/6`.
  have hS_gt : (α * (n : ℝ) / 6) < (S.ncard : ℝ) := by
    have h1 : (S.ncard : ℝ) > α * (n : ℝ) / 4 - 1 := by
      rw [hS]
      have h2 := Nat.lt_floor_add_one (α * (n : ℝ) / 4)
      linarith
    have h2 : (1 : ℝ) ≤ α * (n : ℝ) / 12 := by linarith
    linarith
  -- `|P| = ⌈αn/4⌉`.
  have hPcard : (Pset.ncard : ℝ) = (Nat.ceil (α * (n : ℝ) / 4) : ℝ) := by
    have ncard_coe : ∀ (s : Finset (Fin n)), (↑s : Set (Fin n)).ncard = s.card := by
      intro s
      show ENat.toNat (↑s : Set (Fin n)).encard = s.card
      rw [Set.encard_coe_eq_coe_finsetCard]
      simp
    have hceil_pos : 1 ≤ Nat.ceil (α * (n : ℝ) / 4) :=
      Nat.ceil_pos.mpr (by positivity)
    have h1 : Pset.ncard = Nat.ceil (α * (n : ℝ) / 4) := by
      rw [hPsetdef, ncard_coe, List.toFinset_card_of_nodup ((Walk.isPath_def _).mp hp),
        Walk.length_support, hlen]
      omega
    rw [h1]
  -- `X0 ⊆ P`.
  have hX0sub : X0 ⊆ Pset := by
    intro x hx
    rw [hX0def] at hx
    obtain ⟨hxP, -⟩ := hx
    rw [hPsetdef, Finset.mem_coe, List.mem_toFinset]
    exact hxP
  have hdisj' : ∀ w ∈ Pset, w ∉ S := by
    intro w hw hwS
    rw [hPsetdef, Finset.mem_coe, List.mem_toFinset] at hw
    exact hdisj w hw hwS
  by_contra hcon
  have hlt : (X0.ncard : ℝ) < α ^ 2 * (n : ℝ) / 12 := lt_of_not_ge hcon
  -- Expansion in `G' = G - X0`: for `|U|` between `αn/6` and `n/2`,
  -- `|N_{G'}(U)| ≥ (α/2)|U|`.
  have hexp' : ∀ U : Set ↥X0ᶜ, (α * (n : ℝ) / 6) ≤ (U.ncard : ℝ) →
      (U.ncard : ℝ) ≤ (n : ℝ) / 2 →
      (α / 2) * (U.ncard : ℝ) ≤
        ((CycleLengthsExp.WellSpread.extNbhd G' U).ncard : ℝ) := by
    intro U hUlo hUhi
    set U0 : Set (Fin n) := Subtype.val '' U with hU0def
    have hU0card : (U0.ncard : ℝ) = (U.ncard : ℝ) := by
      rw [hU0def, Set.ncard_image_of_injective _ Subtype.val_injective]
    have himg : Subtype.val '' (CycleLengthsExp.WellSpread.extNbhd G' U) =
        CycleLengthsExp.WellSpread.extNbhd G U0 \ X0 := by
      ext z
      constructor
      · intro hz
        obtain ⟨w, hw, rfl⟩ := hz
        obtain ⟨hwU, u, huU, hadj⟩ := hw
        refine ⟨⟨?_, ⟨(u : Fin n), ⟨u, huU, rfl⟩, hadj⟩⟩, w.2⟩
        intro hzU0
        obtain ⟨u', hu'U, hu'eq⟩ := hzU0
        exact hwU (by have h : u' = w := Subtype.ext hu'eq; rw [h] at hu'U; exact hu'U)
      · intro hz
        obtain ⟨⟨hzU0, u0, hu0U0, hadj⟩, hzX0⟩ := hz
        obtain ⟨u, huU, hu0eq⟩ := hu0U0
        refine ⟨⟨z, hzX0⟩, ⟨?_, u, huU, ?_⟩, rfl⟩
        · intro hmem
          exact hzU0 ⟨⟨z, hzX0⟩, hmem, rfl⟩
        · have hadj' : G.Adj (u : Fin n) z := by
            rw [hu0eq]
            exact hadj
          exact hadj'
    have hcard1 : ((CycleLengthsExp.WellSpread.extNbhd G' U).ncard : ℝ) =
        ((CycleLengthsExp.WellSpread.extNbhd G U0 \ X0).ncard : ℝ) := by
      rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
    have hge : ((CycleLengthsExp.WellSpread.extNbhd G U0).ncard : ℝ) ≤
        ((CycleLengthsExp.WellSpread.extNbhd G U0 \ X0).ncard : ℝ) +
          (X0.ncard : ℝ) := by
      have hsub : CycleLengthsExp.WellSpread.extNbhd G U0 ⊆
          (CycleLengthsExp.WellSpread.extNbhd G U0 \ X0) ∪ X0 := by
        intro z hz
        by_cases hzX : z ∈ X0
        · exact Or.inr hzX
        · exact Or.inl ⟨hz, hzX⟩
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := Set.ncard_union_le (CycleLengthsExp.WellSpread.extNbhd G U0 \ X0) X0
      have h1' : ((CycleLengthsExp.WellSpread.extNbhd G U0).ncard : ℝ) ≤
          (((CycleLengthsExp.WellSpread.extNbhd G U0 \ X0) ∪ X0).ncard : ℝ) := by
        exact_mod_cast h1
      have h2' : (((CycleLengthsExp.WellSpread.extNbhd G U0 \ X0) ∪ X0).ncard : ℝ) ≤
          ((CycleLengthsExp.WellSpread.extNbhd G U0 \ X0).ncard : ℝ) +
            (X0.ncard : ℝ) := by
        exact_mod_cast h2
      linarith
    have hexpG : α * (U0.ncard : ℝ) ≤
        ((CycleLengthsExp.WellSpread.extNbhd G U0).ncard : ℝ) := by
      have hU0le : U0.ncard ≤ (Fintype.card (Fin n) + 1) / 2 := by
        rw [Fintype.card_fin]
        have h1 : U0.ncard ≤ n / 2 := by
          by_contra hcon1
          have h4 : n / 2 + 1 ≤ U0.ncard := by omega
          have h5 : ((n / 2 + 1 : ℕ) : ℝ) ≤ (U0.ncard : ℝ) := by exact_mod_cast h4
          have h6 : (n : ℝ) / 2 < ((n / 2 + 1 : ℕ) : ℝ) := by
            have h7 : n < 2 * (n / 2 + 1) := by omega
            have h8 : (n : ℝ) < 2 * ((n / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h7
            linarith
          have h2 : (U0.ncard : ℝ) ≤ (n : ℝ) / 2 := by
            rw [hU0card]
            exact hUhi
          linarith
        omega
      exact hG U0 hU0le
    rw [hU0card] at hexpG
    have hαU : α ^ 2 * (n : ℝ) / 12 ≤ (α / 2) * (U.ncard : ℝ) := by
      have h1 : (α / 2) * (α * (n : ℝ) / 6) = α ^ 2 * (n : ℝ) / 12 := by
        field_simp
        ring
      rw [← h1]
      exact mul_le_mul_of_nonneg_left hUlo (by linarith : (0 : ℝ) ≤ α / 2)
    have hhalf : (α / 2) * (U.ncard : ℝ) =
        α * (U.ncard : ℝ) - (α / 2) * (U.ncard : ℝ) := by ring
    rw [hcard1]
    linarith [hge, hexpG, hαU, hlt, hU0card, hhalf]
  -- Ball growth in `G'`: either the ball exceeds `n/2`, or it grows by `(1 + α/2)`
  -- at each step.
  have hball : ∀ (Seed : Set ↥X0ᶜ), (α * (n : ℝ) / 6) ≤ (Seed.ncard : ℝ) →
      ∀ r : ℕ, ((n : ℝ) / 2 < ((walkBall G' Seed r).ncard : ℝ)) ∨
        ((1 + α / 2) ^ r * (Seed.ncard : ℝ) ≤ ((walkBall G' Seed r).ncard : ℝ)) := by
    intro Seed hSeed r
    induction r with
    | zero =>
      right
      have hB0 : walkBall G' Seed 0 = Seed := by
        ext w
        constructor
        · intro hw
          obtain ⟨s, hs, q, hq⟩ := hw
          have hq0 : q.length = 0 := Nat.le_zero.mp hq
          cases q with
          | nil => exact hs
          | cons h' q'' => simp [Walk.length_cons] at hq0
        · intro hw
          exact ⟨w, hw, Walk.nil, by simp⟩
      rw [hB0]
      simp
    | succ r ih =>
      rcases ih with h | h
      · left
        have hmono : walkBall G' Seed r ⊆ walkBall G' Seed (r + 1) := by
          intro w hw
          obtain ⟨s, hs, q, hq⟩ := hw
          exact ⟨s, hs, q, le_trans hq (Nat.le_succ r)⟩
        have hle := Set.ncard_le_ncard hmono (Set.toFinite _)
        exact lt_of_lt_of_le h (by exact_mod_cast hle)
      · by_cases hbig : (n : ℝ) / 2 < ((walkBall G' Seed r).ncard : ℝ)
        · left
          have hmono : walkBall G' Seed r ⊆ walkBall G' Seed (r + 1) := by
            intro w hw
            obtain ⟨s, hs, q, hq⟩ := hw
            exact ⟨s, hs, q, le_trans hq (Nat.le_succ r)⟩
          have hle := Set.ncard_le_ncard hmono (Set.toFinite _)
          exact lt_of_lt_of_le hbig (by exact_mod_cast hle)
        · have hBlo : (α * (n : ℝ) / 6) ≤ ((walkBall G' Seed r).ncard : ℝ) := by
            have h1 : (1 : ℝ) ≤ (1 + α / 2) ^ r := one_le_pow₀ (by linarith)
            have h2 : (1 : ℝ) * (Seed.ncard : ℝ) ≤
                (1 + α / 2) ^ r * (Seed.ncard : ℝ) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
            rw [one_mul] at h2
            linarith [h, h2, hSeed]
          have hBhi : ((walkBall G' Seed r).ncard : ℝ) ≤ (n : ℝ) / 2 :=
            le_of_not_gt hbig
          have hexp := hexp' _ hBlo hBhi
          have hsub : walkBall G' Seed r ∪
              CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r) ⊆
              walkBall G' Seed (r + 1) := by
            intro w hw
            rcases hw with hw | hw
            · obtain ⟨s, hs, q, hq⟩ := hw
              exact ⟨s, hs, q, le_trans hq (Nat.le_succ r)⟩
            · obtain ⟨hwU, u, hu, hadj⟩ := hw
              obtain ⟨s, hs, q, hq⟩ := hu
              exact ⟨s, hs, q.concat hadj, by rw [Walk.length_concat]; omega⟩
          have hdisj : Disjoint (walkBall G' Seed r)
              (CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r)) := by
            rw [Set.disjoint_left]
            intro w hw hw2
            obtain ⟨hw2a, -⟩ := hw2
            exact hw2a hw
          have hcard : ((walkBall G' Seed r).ncard : ℝ) +
              ((CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r)).ncard : ℝ) ≤
              ((walkBall G' Seed (r + 1)).ncard : ℝ) := by
            have h1 : ((walkBall G' Seed r ∪
                CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r)).ncard : ℝ) =
                ((walkBall G' Seed r).ncard : ℝ) +
                  ((CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r)).ncard : ℝ) := by
              have h := Set.ncard_union_eq hdisj
              exact_mod_cast h
            have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
            have h2' : ((walkBall G' Seed r ∪
                CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r)).ncard : ℝ) ≤
                ((walkBall G' Seed (r + 1)).ncard : ℝ) := by
              exact_mod_cast h2
            linarith [h1, h2']
          right
          have hgrow : (1 + α / 2) ^ (r + 1) * (Seed.ncard : ℝ) ≤
              (1 + α / 2) * ((walkBall G' Seed r).ncard : ℝ) := by
            have hmul := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 + α / 2)
            calc (1 + α / 2) ^ (r + 1) * (Seed.ncard : ℝ)
                = (1 + α / 2) * ((1 + α / 2) ^ r * (Seed.ncard : ℝ)) := by
                  rw [pow_succ]
                  ring
              _ ≤ (1 + α / 2) * ((walkBall G' Seed r).ncard : ℝ) := hmul
          have hfinal : (1 + α / 2) * ((walkBall G' Seed r).ncard : ℝ) ≤
              ((walkBall G' Seed (r + 1)).ncard : ℝ) := by
            have e : (1 + α / 2) * ((walkBall G' Seed r).ncard : ℝ) =
                ((walkBall G' Seed r).ncard : ℝ) +
                  (α / 2) * ((walkBall G' Seed r).ncard : ℝ) := by ring
            rw [e]
            linarith [hcard, hexp]
          exact le_trans hgrow hfinal
  -- `|S'| = |S|`.
  have hS'card : (S'.ncard : ℝ) = (S.ncard : ℝ) := by
    have himg : Subtype.val '' S' = S := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        have hzX : z ∉ X0 := fun h => hdisj' z (hX0sub h) hz
        exact ⟨⟨z, hzX⟩, hz, rfl⟩
    have h := Set.ncard_image_of_injective S' Subtype.val_injective
    rw [himg] at h
    exact_mod_cast h.symm
  -- `|P'| > αn/6`.
  have hP'card : (P'.ncard : ℝ) > α * (n : ℝ) / 6 := by
    have himg : Subtype.val '' P' = Pset \ X0 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨hw, w.2⟩
      · rintro ⟨hzP, hzX⟩
        exact ⟨⟨z, hzX⟩, hzP, rfl⟩
    have h1 : (P'.ncard : ℝ) = ((Pset \ X0).ncard : ℝ) := by
      have h := Set.ncard_image_of_injective P' Subtype.val_injective
      rw [himg] at h
      exact_mod_cast h.symm
    have h2 : (Pset.ncard : ℝ) ≤ ((Pset \ X0).ncard : ℝ) + (X0.ncard : ℝ) := by
      have hsub : Pset ⊆ (Pset \ X0) ∪ X0 := by
        intro z hz
        by_cases hzX : z ∈ X0
        · exact Or.inr hzX
        · exact Or.inl ⟨hz, hzX⟩
      have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h4 := Set.ncard_union_le (Pset \ X0) X0
      have h3' : (Pset.ncard : ℝ) ≤ (((Pset \ X0) ∪ X0).ncard : ℝ) := by
        exact_mod_cast h3
      have h4' : (((Pset \ X0) ∪ X0).ncard : ℝ) ≤
          ((Pset \ X0).ncard : ℝ) + (X0.ncard : ℝ) := by
        exact_mod_cast h4
      linarith
    have h3 : α ^ 2 * (n : ℝ) ≤ α * (n : ℝ) := by
      calc α ^ 2 * (n : ℝ) = α * (α * (n : ℝ)) := by ring
        _ ≤ 1 * (α * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hα1 (by positivity)
        _ = α * (n : ℝ) := one_mul _
    have hP4 : (α * (n : ℝ) / 4) ≤ (Pset.ncard : ℝ) := by
      rw [hPcard]
      exact Nat.le_ceil _
    rw [h1]
    linarith [h2, hP4, hlt, h3]
  -- Both balls at radius `m` exceed `n/2`.
  have hBS : (n : ℝ) / 2 < ((walkBall G' S' m).ncard : ℝ) := by
    rcases hball S' (by rw [hS'card]; exact le_of_lt hS_gt) m with h | h
    · exact h
    · have h1 : (3 / α) * (α * (n : ℝ) / 6) <
          (1 + α / 2) ^ m * (S'.ncard : ℝ) := by
        have h2 : (3 / α) * (α * (n : ℝ) / 6) < (3 / α) * (S'.ncard : ℝ) :=
          mul_lt_mul_of_pos_left (by rw [hS'card]; exact hS_gt) (by positivity)
        have h3 : (3 / α) * (S'.ncard : ℝ) ≤
            (1 + α / 2) ^ m * (S'.ncard : ℝ) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
        linarith
      have h4 : (3 / α) * (α * (n : ℝ) / 6) = (n : ℝ) / 2 := by
        field_simp
        ring
      linarith [h, h1, h4]
  have hBP : (n : ℝ) / 2 < ((walkBall G' P' m).ncard : ℝ) := by
    rcases hball P' (le_of_lt hP'card) m with h | h
    · exact h
    · have h1 : (3 / α) * (α * (n : ℝ) / 6) <
          (1 + α / 2) ^ m * (P'.ncard : ℝ) := by
        have h2 : (3 / α) * (α * (n : ℝ) / 6) < (3 / α) * (P'.ncard : ℝ) :=
          mul_lt_mul_of_pos_left hP'card (by positivity)
        have h3 : (3 / α) * (P'.ncard : ℝ) ≤
            (1 + α / 2) ^ m * (P'.ncard : ℝ) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
        linarith
      have h4 : (3 / α) * (α * (n : ℝ) / 6) = (n : ℝ) / 2 := by
        field_simp
        ring
      linarith [h, h1, h4]
  -- The two balls intersect.
  obtain ⟨w, hwS, hwP⟩ : ∃ w, w ∈ walkBall G' S' m ∧ w ∈ walkBall G' P' m := by
    by_contra hcon2
    have hcon2' : ∀ w, w ∈ walkBall G' S' m → w ∉ walkBall G' P' m := by
      intro w hw hw2
      exact hcon2 ⟨w, hw, hw2⟩
    have hdisj : Disjoint (walkBall G' S' m) (walkBall G' P' m) := by
      rw [Set.disjoint_left]
      intro x hx hx2
      exact hcon2' x hx hx2
    have hunion : ((walkBall G' S' m ∪ walkBall G' P' m).ncard : ℝ) =
        ((walkBall G' S' m).ncard : ℝ) + ((walkBall G' P' m).ncard : ℝ) := by
      have h := Set.ncard_union_eq hdisj
      exact_mod_cast h
    have hle : ((walkBall G' S' m ∪ walkBall G' P' m).ncard : ℝ) ≤ (n : ℝ) := by
      have h1 := Set.ncard_le_ncard
        (Set.subset_univ (walkBall G' S' m ∪ walkBall G' P' m))
      have h2 : ((Set.univ : Set ↥X0ᶜ).ncard : ℝ) ≤ (n : ℝ) := by
        have h3 : (Set.univ : Set ↥X0ᶜ).ncard = (X0ᶜ).ncard := by
          rw [Set.ncard_univ, Nat.card_coe_set_eq]
        have h4 : (X0ᶜ).ncard = n - X0.ncard := by
          rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
        rw [h3, h4]
        have h5 : X0.ncard ≤ n := by
          have h6 : X0.ncard ≤ Pset.ncard := Set.ncard_le_ncard hX0sub (Set.toFinite _)
          have h7 : Pset.ncard ≤ n := by
            have h8 := Set.ncard_le_ncard (Set.subset_univ Pset) (Set.toFinite _)
            rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h8
          omega
        have h6 : ((n - X0.ncard : ℕ) : ℝ) ≤ (n : ℝ) := by
          rw [Nat.cast_sub h5]
          have h7 : (0 : ℝ) ≤ (X0.ncard : ℝ) := by positivity
          linarith
        exact h6
      have h1' : ((walkBall G' S' m ∪ walkBall G' P' m).ncard : ℝ) ≤
          ((Set.univ : Set ↥X0ᶜ).ncard : ℝ) := by
        exact_mod_cast h1
      linarith
    linarith [hBS, hBP, hunion, hle]
  -- A walk from `S` to `P` in `G'` of length at most `2m`.
  obtain ⟨s₀, hs₀, q₁, hq₁⟩ := hwS
  obtain ⟨y₀, hy₀, q₂, hq₂⟩ := hwP
  obtain ⟨qpath, hqpath, hqplen⟩ :
      ∃ q : G'.Walk s₀ y₀, q.IsPath ∧ q.length ≤ 2 * m := by
    have hwalk : ∃ q : G'.Walk s₀ y₀, q.length ≤ 2 * m := by
      refine ⟨q₁.append q₂.reverse, ?_⟩
      rw [Walk.length_append, Walk.length_reverse]
      omega
    obtain ⟨q, hq⟩ := hwalk
    exact ⟨(q.toPath : G'.Walk s₀ y₀), q.toPath.isPath,
      le_trans q.length_bypass_le_length hq⟩
  -- A shortest path from `S` to `P` in `G'`.
  have hTne : ∃ ℓ, ∃ (s₀ : ↥X0ᶜ), (s₀ : Fin n) ∈ S ∧
      ∃ (y₀ : ↥X0ᶜ), (y₀ : Fin n) ∈ Pset ∧
        ∃ q : G'.Walk s₀ y₀, q.IsPath ∧ q.length = ℓ :=
    ⟨qpath.length, s₀, hs₀, y₀, hy₀, qpath, hqpath, rfl⟩
  set ℓstar := Nat.find hTne with hℓdef
  have hspec := Nat.find_spec hTne
  obtain ⟨s₁, hs₁, y₁, hy₁, q, hqpathMin, hqlen⟩ := hspec
  have hmin : ∀ ℓ, (∃ (s₀ : ↥X0ᶜ), (s₀ : Fin n) ∈ S ∧
      ∃ (y₀ : ↥X0ᶜ), (y₀ : Fin n) ∈ Pset ∧
        ∃ q : G'.Walk s₀ y₀, q.IsPath ∧ q.length = ℓ) → ℓstar ≤ ℓ :=
    fun ℓ hℓ => Nat.find_min' hTne hℓ
  have hℓle : ℓstar ≤ 2 * m := by
    have h1 : ℓstar ≤ qpath.length :=
      hmin _ ⟨s₀, hs₀, y₀, hy₀, qpath, hqpath, rfl⟩
    exact le_trans h1 hqplen
  have hkNum : CycleLengthsExp.ManyLengths.kNum α = 2 * m + 1 := rfl
  -- Internal vertices of the shortest path avoid `S` (else the suffix is shorter).
  have hAvoidS : ∀ j, 0 < j → j < q.length → (q.getVert j : Fin n) ∉ S := by
    intro j hj0 hjlen hmem
    have hmemT : ∃ (s₀ : ↥X0ᶜ), (s₀ : Fin n) ∈ S ∧
        ∃ (y₀ : ↥X0ᶜ), (y₀ : Fin n) ∈ Pset ∧
          ∃ q' : G'.Walk s₀ y₀, q'.IsPath ∧ q'.length = (q.drop j).length :=
      ⟨q.getVert j, hmem, y₁, hy₁, q.drop j, hqpathMin.drop j, rfl⟩
    have hle := hmin _ hmemT
    rw [Walk.drop_length] at hle
    omega
  -- Internal vertices avoid `P` (else the prefix is shorter).
  have hAvoidP : ∀ j, 0 < j → j < q.length → (q.getVert j : Fin n) ∉ Pset := by
    intro j hj0 hjlen hmem
    have hmemT : ∃ (s₀ : ↥X0ᶜ), (s₀ : Fin n) ∈ S ∧
        ∃ (y₀ : ↥X0ᶜ), (y₀ : Fin n) ∈ Pset ∧
          ∃ q' : G'.Walk s₀ y₀, q'.IsPath ∧ q'.length = (q.take j).length :=
      ⟨s₁, hs₁, q.getVert j, hmem, q.take j, hqpathMin.take j, rfl⟩
    have hle := hmin _ hmemT
    rw [Walk.take_length] at hle
    omega
  -- The endpoint `y₁` lies in `X0`: contradiction with `y₁ ∉ X0`.
  have hy1X0 : (y₁ : Fin n) ∈ X0 := by
    refine ⟨?_, ⟨(s₁ : Fin n), hs₁, q.map ⟨Subtype.val, fun h => h⟩, ?_, ?_, ?_⟩⟩
    · have h : (y₁ : Fin n) ∈ Pset := hy₁
      rw [hPsetdef] at h
      exact List.mem_toFinset.mp (Finset.mem_coe.mp h)
    · exact (Walk.isPath_map_iff_of_injective
        (f := (⟨Subtype.val, fun h => h⟩ : G' →g G)) Subtype.val_injective).mpr hqpathMin
    · rw [Walk.length_map, hqlen, hkNum]
      omega
    · intro y hy
      rw [Walk.support_map, List.tail_map', List.dropLast_map'] at hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      show (z : Fin n) ∉ S ∧ (z : Fin n) ∉ p.support
      have hzTail : z ∈ q.support.tail := List.mem_of_mem_dropLast hz
      have hzDrop : z ∈ q.support.dropLast := by
        have hsub : q.support.tail.dropLast ⊆ q.support.dropLast := by
          cases hsup : q.support with
          | nil => simp
          | cons a l =>
            cases l with
            | nil => simp
            | cons b l' =>
              intro w hw
              simp only [List.tail_cons] at hw
              rw [List.dropLast_cons_cons]
              exact List.mem_cons_of_mem a hw
        exact hsub hz
      have hzne : z ≠ s₁ := walk_mem_tail_ne_start hqpathMin hzTail
      have hzne2 : z ≠ y₁ := walk_mem_dropLast_ne_end hqpathMin hzDrop
      obtain ⟨j, hjEq, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp
        (List.mem_of_mem_tail hzTail)
      have hj0 : 0 < j := by
        by_contra hcon0
        have hj0' : j = 0 := by omega
        rw [hj0', Walk.getVert_zero] at hjEq
        exact hzne hjEq.symm
      have hjlt : j < q.length := by
        by_contra hcon0
        have hjeq : j = q.length := by omega
        rw [hjeq, Walk.getVert_length] at hjEq
        exact hzne2 hjEq.symm
      have h1 := hAvoidS j hj0 hjlt
      have h2 := hAvoidP j hj0 hjlt
      rw [hjEq] at h1 h2
      constructor
      · exact h1
      · intro hmem
        exact h2 (by rw [hPsetdef]; exact Finset.mem_coe.mpr (List.mem_toFinset.mpr hmem))
  exact y₁.2 hy1X0


theorem bfs_parent_tree_proved {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Set V) (v₀ : V) (hv₀ : v₀ ∈ S)
    (hreach : ∀ v ∈ S, G.Reachable v₀ v)
    (hparent : ∀ v ∈ S, v ≠ v₀ →
      ∃ u ∈ S, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v) :
    ∃ T : G.Subgraph, T.verts = S ∧ T.spanningCoe.IsAcyclic ∧
      (∀ v ∈ S, T.spanningCoe.Reachable v₀ v) ∧
      (∀ v ∈ S, T.spanningCoe.dist v₀ v = G.dist v₀ v) := by
  classical
  -- Parent function from the hypothesis, pinned at the root.
  -- First totalize the choice so `choose` yields a plain `V → V`.
  have hex : ∀ v : V, ∃ u : V,
      (v ∈ S ∧ v ≠ v₀ → u ∈ S ∧ G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v) ∧
        (v = v₀ → u = v₀) := by
    intro v
    by_cases hv : v ∈ S ∧ v ≠ v₀
    · obtain ⟨u, huS, hAdj, hdist⟩ := hparent v hv.1 hv.2
      exact ⟨u, fun _ => ⟨huS, hAdj, hdist⟩, fun hEq => absurd hEq hv.2⟩
    · exact ⟨v₀, fun h => absurd h hv, fun _ => rfl⟩
  choose par' hpar' using hex
  have hpar'0 : par' v₀ = v₀ := (hpar' v₀).2 rfl
  have hpar'' : ∀ v ∈ S, v ≠ v₀ →
      par' v ∈ S ∧ G.Adj (par' v) v ∧ G.dist v₀ (par' v) + 1 = G.dist v₀ v :=
    fun v hv hne => (hpar' v).1 ⟨hv, hne⟩
  -- T: the parent-edge subgraph on S.
  set T : G.Subgraph :=
    { verts := S
      Adj := fun u v => u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ (par' u = v ∨ par' v = u)
      adj_sub := by
        intro u v h
        obtain ⟨huS, hvS, huv, hpar⟩ := h
        rcases hpar with h1 | h1
        · have hu0 : u ≠ v₀ := by
            rintro rfl
            rw [hpar'0] at h1
            exact huv h1
          obtain ⟨_, hAdj, _⟩ := hpar'' u huS hu0
          rw [h1] at hAdj
          exact hAdj.symm
        · have hv0 : v ≠ v₀ := by
            rintro rfl
            rw [hpar'0] at h1
            exact huv h1.symm
          obtain ⟨_, hAdj, _⟩ := hpar'' v hvS hv0
          rw [h1] at hAdj
          exact hAdj
      edge_vert := by
        intro u v h
        exact h.1
      symm := ⟨fun {u v} h =>
        ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩⟩ } with hTdef
  have hTverts : T.verts = S := by rw [hTdef]
  have hTadj_iff : ∀ {u v : V}, T.Adj u v ↔
      (u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ (par' u = v ∨ par' v = u)) := by
    intro u v
    rw [hTdef]
  -- Parent chain: a T-walk from v to v₀ of length dist_G(v₀, v).
  have hchain : ∀ k : ℕ, ∀ v ∈ S, G.dist v₀ v = k →
      ∃ p : T.spanningCoe.Walk v v₀, p.length = k := by
    intro k
    induction k with
    | zero =>
      intro v hv hd
      have hv0 : v = v₀ := by
        have h0 := hd
        rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable] at h0
        rcases h0 with hEq | hnr
        · exact hEq.symm
        · exact absurd (hreach v hv) hnr
      subst hv0
      exact ⟨Walk.nil, rfl⟩
    | succ k ih =>
      intro v hv hd
      have hne : v ≠ v₀ := by
        rintro rfl
        simp at hd
      obtain ⟨hparS, _hparAdj, hparDist⟩ := hpar'' v hv hne
      have hdk : G.dist v₀ (par' v) = k := by omega
      obtain ⟨p, hp⟩ := ih (par' v) hparS hdk
      have hne2 : v ≠ par' v := by
        rintro hEq
        rw [← hEq] at hparDist
        omega
      have hT : T.Adj v (par' v) :=
        hTadj_iff.mpr ⟨hv, hparS, hne2, Or.inl rfl⟩
      have hT' : T.spanningCoe.Adj v (par' v) := by
        rw [Subgraph.spanningCoe_adj]
        exact hT
      exact ⟨Walk.cons hT' p, by simp [Walk.length_cons, hp]⟩
  have hreachT : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v := by
    intro v hv
    obtain ⟨p, _hp⟩ := hchain (G.dist v₀ v) v hv rfl
    exact ⟨p.reverse⟩
  -- Every T-walk maps to a G-walk of the same length.
  have hmap : ∀ {a b : V} (p : T.spanningCoe.Walk a b),
      ∃ q : G.Walk a b, q.length = p.length := by
    intro a b p
    induction p with
    | nil => exact ⟨Walk.nil, rfl⟩
    | cons h p ih =>
      obtain ⟨q, hq⟩ := ih
      exact ⟨Walk.cons (T.adj_sub h) q, by simp [Walk.length_cons, hq]⟩
  have hdist_le : ∀ v ∈ S, T.spanningCoe.dist v₀ v ≤ G.dist v₀ v := by
    intro v hv
    obtain ⟨p, hp⟩ := hchain (G.dist v₀ v) v hv rfl
    have hle := SimpleGraph.dist_le (G := T.spanningCoe) p.reverse
    rwa [Walk.length_reverse, hp] at hle
  have hdist_ge : ∀ v ∈ S, G.dist v₀ v ≤ T.spanningCoe.dist v₀ v := by
    intro v hv
    obtain ⟨p, hp⟩ := (hreachT v hv).exists_walk_length_eq_dist
    obtain ⟨q, hq⟩ := hmap p
    have hle := SimpleGraph.dist_le (G := G) q
    rwa [hq, hp] at hle
  -- Acyclicity: a cycle's max-distance vertex would need two distinct
  -- neighbours, but only its parent can be a neighbour at ≤ its distance.
  have hacyc : T.spanningCoe.IsAcyclic := by
    intro v c hc
    obtain ⟨x0, hx0⟩ := c.support_nonempty
    have hne : c.support.toFinset.Nonempty := ⟨x0, List.mem_toFinset.mpr hx0⟩
    obtain ⟨x, hxfin, hxmax⟩ :=
      Finset.exists_max_image c.support.toFinset (fun w => G.dist v₀ w) hne
    have hx : x ∈ c.support := List.mem_toFinset.mp hxfin
    have hcard : (c.toSubgraph.neighborSet x).ncard = 2 :=
      hc.ncard_neighborSet_toSubgraph_eq_two hx
    have hsub : c.toSubgraph.neighborSet x ⊆ {par' x} := by
      intro w hw
      rw [Subgraph.mem_neighborSet] at hw
      have hmem : s(x, w) ∈ c.edges := Walk.adj_toSubgraph_iff_mem_edges.mp hw
      have hTadj : T.spanningCoe.Adj x w := c.adj_of_mem_edges hmem
      obtain ⟨_hxS, hwS, hxw, hpar⟩ := hTadj_iff.mp hTadj
      rcases hpar with h1 | h1
      · exact Set.mem_singleton_iff.mpr h1.symm
      · exfalso
        have hw0 : w ≠ v₀ := by
          rintro rfl
          rw [hpar'0] at h1
          exact hxw h1.symm
        obtain ⟨_, _, hdist⟩ := hpar'' w hwS hw0
        rw [h1] at hdist
        have hwsup : w ∈ c.support := Walk.mem_support_of_adj_toSubgraph hw.symm
        have hmax : G.dist v₀ w ≤ G.dist v₀ x :=
          hxmax w (List.mem_toFinset.mpr hwsup)
        omega
    have hle : (c.toSubgraph.neighborSet x).ncard ≤ 1 := by
      calc (c.toSubgraph.neighborSet x).ncard
          ≤ ({par' x} : Set V).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_singleton _)
        _ = 1 := Set.ncard_singleton _
    omega
  exact ⟨T, hTverts, hacyc, hreachT,
    fun v hv => le_antisymm (hdist_le v hv) (hdist_ge v hv)⟩

theorem h42_pred {V : Type*} {G : SimpleGraph V} {v₀ v : V} (hr : G.Reachable v₀ v) (hne : v ≠ v₀) :
    ∃ u, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hpr : p.reverse.length = G.dist v₀ v := by rw [SimpleGraph.Walk.length_reverse, hp]
  generalize p.reverse = q at hpr
  cases q with
  | nil => exact absurd rfl hne
  | @cons _ u _ h q =>
    refine ⟨u, h.symm, ?_⟩
    have h1 : G.dist u v₀ ≤ q.length := SimpleGraph.dist_le q
    rw [SimpleGraph.Walk.length_cons] at hpr
    have h2 : G.dist v₀ v ≤ G.dist v₀ u + G.dist u v := h.symm.reachable.dist_triangle_right v₀
    have h3 : G.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h.symm
    rw [SimpleGraph.dist_comm] at h1
    omega

theorem bfs_prefix_set_proved (n : ℕ) (G : SimpleGraph (Fin n)) (v₀ : Fin n) (N : ℕ)
    (hconn : ∀ v, G.Reachable v₀ v) (hN1 : 1 ≤ N) (hNn : N ≤ n) :
    ∃ (S : Set (Fin n)) (r : ℕ),
      S.ncard = N ∧ v₀ ∈ S ∧
      (∀ v, G.dist v₀ v ≤ r - 1 → v ∈ S) ∧
      (∀ v ∈ S, G.dist v₀ v ≤ r) ∧
      (∃ v ∈ S, G.dist v₀ v = r) ∧
      (∀ v ∈ S, v ≠ v₀ →
        ∃ u ∈ S, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v) := by
  classical
  let B : ℕ → Finset (Fin n) := fun k => Finset.univ.filter (fun v => G.dist v₀ v ≤ k)
  have hex : ∃ k, N ≤ (B k).card := by
    refine ⟨Finset.univ.sup (fun v => G.dist v₀ v), ?_⟩
    have : B (Finset.univ.sup (fun v => G.dist v₀ v)) = Finset.univ := by
      ext v; simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Finset.le_sup (f := fun v => G.dist v₀ v) (Finset.mem_univ v)
    rw [this, Finset.card_univ, Fintype.card_fin]; exact hNn
  let r := Nat.find hex
  have hr : N ≤ (B r).card := Nat.find_spec hex
  let A : Finset (Fin n) := Finset.univ.filter (fun v => G.dist v₀ v < r)
  let Sp : Finset (Fin n) := Finset.univ.filter (fun v => G.dist v₀ v = r)
  have hA : A.card < N := by
    by_cases h0 : r = 0
    · have : A = ∅ := by
        ext v; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
      rw [this, Finset.card_empty]; omega
    · have hm := Nat.find_min hex (show r - 1 < r by omega)
      have : A = B (r - 1) := by
        ext v; simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [this]; omega
  have hBr : B r = A ∪ Sp := by
    ext v; simp only [A, B, Sp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
  have hdisj : Disjoint A Sp := by
    rw [Finset.disjoint_left]; intro v h1 h2
    simp only [A, Sp, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
  have hSp : N - A.card ≤ Sp.card := by
    rw [hBr, Finset.card_union_of_disjoint hdisj] at hr; omega
  obtain ⟨Q, hQSp, hQcard⟩ := Finset.exists_subset_card_eq hSp
  have hQne : Q.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨q, hq⟩ := hQne
  have hqr : G.dist v₀ q = r := by
    have := hQSp hq; simp only [Sp, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
  have hdisjQ : Disjoint A Q := Finset.disjoint_of_subset_right hQSp hdisj
  have memS : ∀ v, v ∈ ((A ∪ Q : Finset (Fin n)) : Set (Fin n)) ↔ v ∈ A ∨ v ∈ Q := by
    intro v; simp
  have hle : ∀ v, v ∈ A ∨ v ∈ Q → G.dist v₀ v ≤ r := by
    intro v hv
    rcases hv with hv | hv
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hv; omega
    · have := hQSp hv; simp only [Sp, Finset.mem_filter, Finset.mem_univ, true_and] at this; omega
  have hv₀S : v₀ ∈ A ∨ v₀ ∈ Q := by
    by_cases h0 : r = 0
    · right
      have : q = v₀ := by
        have := ((hconn q).dist_eq_zero_iff).mp (by omega); exact this.symm
      rw [← this]; exact hq
    · left; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.dist_self]; omega
  refine ⟨((A ∪ Q : Finset (Fin n)) : Set (Fin n)), r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisjQ]; omega
  · exact (memS v₀).mpr hv₀S
  · intro v hv
    rw [memS]
    by_cases h0 : r = 0
    · have : v = v₀ := (((hconn v).dist_eq_zero_iff).mp (by omega)).symm
      rw [this]; exact hv₀S
    · left; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro v hv; exact hle v ((memS v).mp hv)
  · exact ⟨q, (memS q).mpr (Or.inr hq), hqr⟩
  · intro v hv hne
    obtain ⟨u, hu, hdu⟩ := h42_pred (hconn v) hne
    have hvr := hle v ((memS v).mp hv)
    refine ⟨u, (memS u).mpr (Or.inl ?_), hu, hdu⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; omega

theorem bfs_tree_prefix_proof (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hn : 12 ≤ α * (n : ℝ)) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) :
    ∃ (S : Set (Fin n)) (T : G.Subgraph) (v₀ : Fin n) (m : ℕ),
      S.ncard = Nat.floor (α * (n : ℝ) / 4) ∧
      T.verts = S ∧
      v₀ ∈ S ∧
      T.spanningCoe.IsAcyclic ∧
      (∀ v ∈ S, T.spanningCoe.Reachable v₀ v) ∧
      (∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v ≤ m) ∧
      (∃ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = m) ∧
      (∀ t ∈ S, ∀ q : Fin n, q ∉ S → G.Adj t q →
        m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀ t) := by
  classical
  -- `n ≥ 1` from `α * n ≥ 12`.
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num at hn
    · exact h
  -- The expander hypothesis, unfolded once.
  have hG' : ∀ U : Set (Fin n), U.ncard ≤ (Fintype.card (Fin n) + 1) / 2 →
      α * (U.ncard : ℝ) ≤
        (CycleLengthsExp.WellSpread.extNbhd G U).ncard := hG
  rw [Fintype.card_fin] at hG'
  -- Connectivity: every vertex is reachable from any fixed v₀.
  -- Let U = reachable set from v₀. extNbhd(U) = ∅ (a neighbour of a
  -- reachable vertex is reachable), so if |U| ≤ (n+1)/2 expansion forces
  -- |U| = 0, contradicting v₀ ∈ U; hence |U| > (n+1)/2. The same
  -- argument on Uᶜ (whose external neighbourhood is also empty: a
  -- neighbour in U of a vertex of Uᶜ would make it reachable) forces
  -- |Uᶜ| = 0, so U = univ.
  have hconn : ∀ (v₀ : Fin n) (v : Fin n), G.Reachable v₀ v := by
    intro v₀ v
    set U : Set (Fin n) := {w | G.Reachable v₀ w} with hUdef
    have hU0 : v₀ ∈ U := SimpleGraph.Reachable.refl v₀
    have hUnbhd : CycleLengthsExp.WellSpread.extNbhd G U = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      obtain ⟨hzU, u, hu, hAdj⟩ := hz
      exact hzU (hu.trans ⟨Walk.cons hAdj Walk.nil⟩)
    have hcompl_nbhd : CycleLengthsExp.WellSpread.extNbhd G Uᶜ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      obtain ⟨hzUc, u, hu, hAdj⟩ := hz
      -- z ∈ U (else z ∈ Uᶜ), u ∈ Uᶜ, Adj u z: then u is reachable via z.
      have hzU : z ∈ U := Set.notMem_compl_iff.mp hzUc
      have huU : u ∈ U := (hzU.trans ⟨Walk.cons hAdj.symm Walk.nil⟩)
      exact hu huU
    have hUcard : U.ncard + Uᶜ.ncard = n := by
      have h := Set.ncard_add_ncard_compl U (Set.toFinite U) (Set.toFinite Uᶜ)
      rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
      exact h
    have hUgt : (n + 1) / 2 < U.ncard := by
      by_contra hle
      rw [not_lt] at hle
      have hexp := hG' U hle
      rw [hUnbhd, Set.ncard_empty, Nat.cast_zero] at hexp
      have hpos : (0 : ℝ) < α * (U.ncard : ℝ) := by
        apply mul_pos hα0
        have h1 : 0 < U.ncard := Iff.mpr (Set.ncard_pos (s := U)) ⟨v₀, hU0⟩
        exact_mod_cast h1
      linarith
    have hcompl_le : Uᶜ.ncard ≤ (n + 1) / 2 := by omega
    have hexp2 := hG' Uᶜ hcompl_le
    rw [hcompl_nbhd, Set.ncard_empty, Nat.cast_zero] at hexp2
    have hcompl0 : Uᶜ.ncard = 0 := by
      by_contra hne
      have hpos : (0 : ℝ) < α * (Uᶜ.ncard : ℝ) := by
        apply mul_pos hα0
        exact_mod_cast Nat.pos_of_ne_zero hne
      linarith
    have hUuniv : U = Set.univ := by
      rw [← Set.compl_empty_iff, ← Set.ncard_eq_zero (Set.toFinite Uᶜ)]
      exact hcompl0
    have hUuniv : U = Set.univ := by
      rw [← Set.compl_empty_iff, ← Set.ncard_eq_zero (Set.toFinite Uᶜ)]
      exact hcompl0
    have hvmem : v ∈ U := by rw [hUuniv]; exact Set.mem_univ v
    exact hvmem
  -- The root and the target size.
  set v₀ : Fin n := ⟨0, hn0⟩ with hv₀def
  have hN1 : 1 ≤ Nat.floor (α * (n : ℝ) / 4) :=
    Nat.floor_pos.mpr (by linarith)
  have hNn : Nat.floor (α * (n : ℝ) / 4) ≤ n := by
    have h1 : ((Nat.floor (α * (n : ℝ) / 4) : ℕ) : ℝ) ≤ α * (n : ℝ) / 4 :=
      Nat.floor_le (by positivity)
    have h2 : α * (n : ℝ) / 4 ≤ (n : ℝ) := by
      have h3 : α * (n : ℝ) ≤ (n : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hα1 (show (0 : ℝ) ≤ (n : ℝ) by positivity)
        simpa using h
      linarith
    exact_mod_cast le_trans h1 h2
  obtain ⟨S, r, hScard, hv₀S, hprefix, hSle, hSmax, hparent⟩ :=
    bfs_prefix_set_proved n G v₀ _ (fun v => hconn v₀ v) hN1 hNn
  have hreachS : ∀ v ∈ S, G.Reachable v₀ v := fun v _ => hconn v₀ v
  obtain ⟨T, hTverts, hTacyc, hTreach, hTdist⟩ :=
    bfs_parent_tree_proved G S v₀ hv₀S hreachS hparent
  -- Level = dist_T + 1 = dist_G + 1 on S.
  have hlev : ∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = G.dist v₀ v + 1 := by
    intro v hv
    show T.spanningCoe.dist v₀ v + 1 = G.dist v₀ v + 1
    rw [hTdist v hv]
  refine ⟨S, T, v₀, r + 1, hScard, hTverts, hv₀S, hTacyc, hTreach, ?_, ?_, ?_⟩
  · intro v hv
    rw [hlev v hv]
    have := hSle v hv
    omega
  · obtain ⟨v, hv, hvr⟩ := hSmax
    exact ⟨v, hv, by rw [hlev v hv, hvr]⟩
  · intro t ht q hq hAdj
    rw [hlev t ht]
    -- If dist(t) ≤ r - 2 then dist(q) ≤ dist(t) + 1 ≤ r - 1, so q ∈ S
    -- by the prefix property — contradiction. Hence r ≤ dist(t) + 1.
    by_contra hlt
    rw [not_le] at hlt
    have hdistq : G.dist v₀ q ≤ G.dist v₀ t + 1 := by
      obtain ⟨p, hp⟩ := (hconn v₀ t).exists_walk_length_eq_dist
      have h := SimpleGraph.dist_le (p.concat hAdj)
      rw [Walk.length_concat, hp] at h
      exact h
    have hqS : q ∈ S := hprefix q (by omega)
    exact hq hqS


/-- List helper: membership in `dropLast` of a cons-list is membership in
`dropLast` of the tail, or equality with the head. Proved for real. -/
theorem dropLast_head {V : Type*} (a : V) (l : List V) (y : V)
    (hy : y ∈ (a :: l).dropLast) : y ∈ l.dropLast ∨ y = a := by
  cases l with
  | nil => simp at hy
  | cons b l' =>
    have heq : (a :: b :: l').dropLast = a :: (b :: l').dropLast := rfl
    rw [heq] at hy
    rcases List.mem_cons.mp hy with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem h42_acyc {V : Type*} [DecidableEq V] {H H' : SimpleGraph V} (hH' : H'.IsAcyclic)
    (h : V → ℕ) (p : V → V)
    (hadj : ∀ a b, H.Adj a b → H'.Adj a b ∨ (p a = b ∧ 0 < h a ∧ h b + 1 = h a) ∨
      (p b = a ∧ 0 < h b ∧ h a + 1 = h b))
    (h0 : ∀ a b, H'.Adj a b → h a = 0) : H.IsAcyclic := by
  intro x c hc
  by_cases hpos : ∃ y ∈ c.support, 0 < h y
  · obtain ⟨y, hy, hymax⟩ := c.support.toFinset.exists_max_image h ⟨x, by simp⟩
    rw [List.mem_toFinset] at hy
    have hmax : ∀ z ∈ c.support, h z ≤ h y := fun z hz => hymax z (List.mem_toFinset.mpr hz)
    have hypos : 0 < h y := by
      obtain ⟨z, hz, hz'⟩ := hpos; exact lt_of_lt_of_le hz' (hmax z hz)
    have hc' : (c.rotate y hy).IsCycle := hc.rotate hy
    have hnn : ¬ (c.rotate y hy).Nil := hc'.not_nil
    have key : ∀ z, H.Adj y z → z ∈ (c.rotate y hy).support → z = p y := by
      intro z hyz hz
      rw [SimpleGraph.Walk.mem_support_rotate_iff] at hz
      rcases hadj y z hyz with h1 | ⟨h1, _, _⟩ | ⟨h1, _, h3⟩
      · have := h0 y z h1; omega
      · exact h1.symm
      · have := hmax z hz; omega
    have e1 := key _ (SimpleGraph.Walk.adj_snd hnn) (SimpleGraph.Walk.getVert_mem_support _ _)
    have e2 := key _ (SimpleGraph.Walk.adj_penultimate hnn).symm
      (SimpleGraph.Walk.getVert_mem_support _ _)
    exact hc'.snd_ne_penultimate (e1.trans e2.symm)
  · push Not at hpos
    have hE : ∀ e ∈ c.edges, e ∈ H'.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        have ha := hpos a (c.fst_mem_support_of_mem_edges he)
        have hb := hpos b (c.snd_mem_support_of_mem_edges he)
        have hab : H.Adj a b := c.adj_of_mem_edges he
        rcases hadj a b hab with h1 | ⟨_, h2, _⟩ | ⟨_, h2, _⟩
        · exact h1
        · omega
        · omega
    exact hH' (c.transfer H' hE) (hc.transfer hE)

theorem ext_parent_tree_ax {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Set V) (T : G.Subgraph) (v₀ : V)
    (hTverts : T.verts = S) (hv₀ : v₀ ∈ S)
    (hTacyc : T.spanningCoe.IsAcyclic)
    (hTreach : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v)
    (W : Set V) (hSW : S ⊆ W)
    (h : V → ℕ) (hhS : ∀ w ∈ S, h w = 0) (hhW : ∀ w ∈ W, w ∉ S → 0 < h w)
    (hparent : ∀ w ∈ W, w ∉ S → ∃ u ∈ W, G.Adj u w ∧ h u + 1 = h w) :
    ∃ (T₁ : G.Subgraph) (r : V → V),
      T₁.verts = W ∧
      (∀ a b, T.spanningCoe.Adj a b → T₁.spanningCoe.Adj a b) ∧
      T₁.spanningCoe.IsAcyclic ∧
      (∀ w ∈ W, T₁.spanningCoe.Reachable v₀ w) ∧
      (∀ w ∈ W, r w ∈ S) ∧
      (∀ w ∈ S, r w = w) ∧
      (∀ w ∈ W, T₁.spanningCoe.dist v₀ w = T.spanningCoe.dist v₀ (r w) + h w) ∧
      (∀ w ∈ W, w ∉ S → ∃ z, z ∉ S ∧ G.Adj (r w) z) := by
  classical
  have hpex : ∀ w, ∃ u, w ∈ W → w ∉ S → u ∈ W ∧ G.Adj u w ∧ h u + 1 = h w := by
    intro w
    by_cases hw : w ∈ W ∧ w ∉ S
    · obtain ⟨u, hu, hadj, hh⟩ := hparent w hw.1 hw.2
      exact ⟨u, fun _ _ => ⟨hu, hadj, hh⟩⟩
    · exact ⟨w, fun a b => absurd ⟨a, b⟩ hw⟩
  choose p hp using hpex
  have hWS : ∀ x ∈ W, h x = 0 → x ∈ S := by
    intro x hx h0; by_contra hxS; have := hhW x hx hxS; omega
  have hit : ∀ k x, x ∈ W → k ≤ h x → p^[k] x ∈ W ∧ h (p^[k] x) + k = h x := by
    intro k
    induction k with
    | zero => intro x hx _; exact ⟨hx, by simp⟩
    | succ k ih =>
      intro x hx hk
      obtain ⟨h1, h2⟩ := ih x hx (by omega)
      have hyS : p^[k] x ∉ S := by intro hS; have := hhS _ hS; omega
      obtain ⟨h3, _, h5⟩ := hp _ h1 hyS
      rw [Function.iterate_succ_apply']
      exact ⟨h3, by omega⟩
  let r : V → V := fun x => p^[h x] x
  have hrS : ∀ w ∈ W, r w ∈ S := by
    intro w hw
    obtain ⟨h1, h2⟩ := hit (h w) w hw le_rfl
    have h0 : h (p^[h w] w) = 0 := by omega
    exact hWS _ h1 h0
  have hrid : ∀ w ∈ S, r w = w := by
    intro w hw; show p^[h w] w = w; rw [hhS w hw]; rfl
  have hrp : ∀ x ∈ W, x ∉ S → r (p x) = r x := by
    intro x hx hxS
    have hh := (hp x hx hxS).2.2
    show p^[h (p x)] (p x) = p^[h x] x
    rw [← hh, Function.iterate_succ_apply]
  let T₁ : G.Subgraph :=
    { verts := W
      Adj := fun a b => T.Adj a b ∨ (a ∈ W ∧ a ∉ S ∧ p a = b) ∨ (b ∈ W ∧ b ∉ S ∧ p b = a)
      adj_sub := by
        rintro a b (h1 | ⟨ha, haS, rfl⟩ | ⟨hb, hbS, rfl⟩)
        · exact T.adj_sub h1
        · exact (hp a ha haS).2.1.symm
        · exact (hp b hb hbS).2.1
      edge_vert := by
        rintro a b (h1 | ⟨ha, _, _⟩ | ⟨hb, hbS, rfl⟩)
        · exact hSW (hTverts ▸ T.edge_vert h1)
        · exact ha
        · exact (hp b hb hbS).1
      symm := ⟨fun a b hab => by
        rcases hab with h1 | h2 | h3
        · exact Or.inl (T.adj_symm h1)
        · exact Or.inr (Or.inr h2)
        · exact Or.inr (Or.inl h3)⟩ }
  have hT1adj : ∀ a b, T₁.spanningCoe.Adj a b ↔
      (T.Adj a b ∨ (a ∈ W ∧ a ∉ S ∧ p a = b) ∨ (b ∈ W ∧ b ∉ S ∧ p b = a)) := fun a b => Iff.rfl
  have hTS : ∀ a b, T.Adj a b → a ∈ S := fun a b hab => hTverts ▸ T.edge_vert hab
  have hle : T.spanningCoe ≤ T₁.spanningCoe := fun a b hab => Or.inl hab
  -- upper bound walks
  have hup : ∀ k, ∀ x ∈ W, h x = k →
      ∃ q : T₁.spanningCoe.Walk v₀ x, q.length = T.spanningCoe.dist v₀ (r x) + h x := by
    intro k
    induction k with
    | zero =>
      intro x hx hx0
      have hxS := hWS x hx hx0
      obtain ⟨q, hq⟩ := (hTreach x hxS).exists_walk_length_eq_dist
      refine ⟨q.mapLe hle, ?_⟩
      rw [SimpleGraph.Walk.length_mapLe, hq, hrid x hxS, hx0]; rfl
    | succ k ih =>
      intro x hx hxk
      have hxS : x ∉ S := by intro hS; have := hhS x hS; omega
      obtain ⟨h1, _, h3⟩ := hp x hx hxS
      obtain ⟨q, hq⟩ := ih (p x) h1 (by omega)
      have hadj : T₁.spanningCoe.Adj (p x) x := Or.inr (Or.inr ⟨hx, hxS, rfl⟩)
      refine ⟨q.concat hadj, ?_⟩
      rw [SimpleGraph.Walk.length_concat, hq, hrp x hx hxS]; omega
  -- lower bound
  have hlow : ∀ a b (q : T₁.spanningCoe.Walk a b), a ∈ W →
      T.spanningCoe.dist v₀ (r a) + h a ≤ T.spanningCoe.dist v₀ (r b) + h b + q.length := by
    intro a b q
    induction q with
    | nil => intro _; simp
    | @cons a a' b hadj q ih =>
      intro ha
      have ha' : a' ∈ W := T₁.edge_vert hadj.symm
      have := ih ha'
      rw [SimpleGraph.Walk.length_cons]
      rcases hadj with h1 | ⟨_, haS, rfl⟩ | ⟨_, haS', rfl⟩
      · have haS := hTS a a' h1
        have haS' := hTS a' a (T.adj_symm h1)
        rw [hrid a haS, hrid a' haS', hhS a haS, hhS a' haS'] at *
        have hr : T.spanningCoe.Reachable a' a := (SimpleGraph.Adj.reachable (G := T.spanningCoe) (T.adj_symm h1))
        have h2 := hr.dist_triangle_right v₀
        have h3 : T.spanningCoe.dist a' a = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr (show T.spanningCoe.Adj a' a from T.adj_symm h1)
        omega
      · have := (hp a ha haS).2.2
        rw [← hrp a ha haS]; omega
      · have := (hp a' ha' haS').2.2
        rw [hrp a' ha' haS'] at *; omega
  have hreach : ∀ w ∈ W, T₁.spanningCoe.Reachable v₀ w := by
    intro w hw; obtain ⟨q, _⟩ := hup (h w) w hw rfl; exact ⟨q⟩
  have hfront : ∀ k, ∀ w ∈ W, w ∉ S → h w = k + 1 → ∃ z, z ∉ S ∧ G.Adj (r w) z := by
    intro k
    induction k with
    | zero =>
      intro w hw hwS hk
      obtain ⟨h1, h2, h3⟩ := hp w hw hwS
      have hpS := hWS _ h1 (by omega)
      refine ⟨w, hwS, ?_⟩
      rw [← hrp w hw hwS, hrid _ hpS]; exact h2
    | succ k ih =>
      intro w hw hwS hk
      obtain ⟨h1, _, h3⟩ := hp w hw hwS
      have hpS : p w ∉ S := by intro hS; have := hhS _ hS; omega
      rw [← hrp w hw hwS]; exact ih (p w) h1 hpS (by omega)
  refine ⟨T₁, r, rfl, fun a b hab => Or.inl hab, ?_, hreach, hrS, hrid, ?_, ?_⟩
  · refine h42_acyc hTacyc h p ?_ ?_
    · intro a b hab
      rcases hab with h1 | ⟨ha, haS, rfl⟩ | ⟨hb, hbS, rfl⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨rfl, hhW a ha haS, (hp a ha haS).2.2⟩)
      · exact Or.inr (Or.inr ⟨rfl, hhW b hb hbS, (hp b hb hbS).2.2⟩)
    · intro a b hab; exact hhS a (hTS a b hab)
  · intro w hw
    obtain ⟨q, hq⟩ := hup (h w) w hw rfl
    obtain ⟨q', hq'⟩ := (hreach w hw).exists_walk_length_eq_dist
    have h1 := hlow w v₀ q'.reverse hw
    rw [hrid v₀ hv₀, hhS v₀ hv₀, SimpleGraph.Walk.length_reverse, hq'] at h1
    simp only [SimpleGraph.dist_self] at h1
    have h2 := SimpleGraph.dist_le q
    omega
  · intro w hw hwS
    have := hhW w hw hwS
    exact hfront (h w - 1) w hw hwS (by omega)

/-
DEEP INPUT B2 — PROVED (2026-10-17). Distance to `S` avoiding `P` + predecessor.
Pure graph theory (no expansion): `W` is the set of vertices reachable
from `S` by a walk whose support avoids `P`, and `h w` is the shortest
such walk length. The parent property is the predecessor on a shortest
walk; minimality says `h w` is at most any avoiding-walk length.
Proof: `h w = sInf` of avoiding-walk lengths; `sInf_mem` gives a shortest
walk; its penultimate vertex (via `Walk.dropLast` / `Walk.adj_penultimate`)
has `h` one less, and concatenating the last edge gives `h w ≤ h z + 1`.
Standalone proof file: `tree_extension_attach_b2.lean` (theorem `dist_avoid_pred`).
-/
/-- List helper: membership in `dropLast` implies membership. Proved for real. -/
theorem mem_of_mem_dropLast {V : Type*} (l : List V) (y : V)
    (hy : y ∈ l.dropLast) : y ∈ l := by
  induction l with
  | nil => simp at hy
  | cons a l' ih =>
    cases l' with
    | nil => simp at hy
    | cons b l'' =>
      have heq : (a :: b :: l'').dropLast = a :: (b :: l'').dropLast := rfl
      rw [heq] at hy
      rcases List.mem_cons.mp hy with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem dist_avoid_pred_ax (n : ℕ) (G : SimpleGraph (Fin n))
    (S : Set (Fin n)) (P : Set (Fin n)) (hdisj : ∀ w ∈ P, w ∉ S) :
    ∃ (W : Set (Fin n)) (h : Fin n → ℕ),
      S ⊆ W ∧ (∀ w ∈ W, w ∉ P) ∧
      (∀ w ∈ S, h w = 0) ∧ (∀ w ∈ W, w ∉ S → 0 < h w) ∧
      (∀ w ∈ W, w ∉ S → ∃ u ∈ W, G.Adj u w ∧ h u + 1 = h w) ∧
      (∀ w, w ∈ W ↔ w ∉ P ∧ ∃ s ∈ S, ∃ q : G.Walk s w, ∀ y ∈ q.support, y ∉ P) ∧
      (∀ w ∈ W, ∀ s ∈ S, ∀ q : G.Walk s w,
        (∀ y ∈ q.support, y ∉ P) → h w ≤ q.length) := by
  classical
  -- Avoiding-walk lengths to `w`.
  set D : Fin n → Set ℕ := fun w =>
    {ℓ | ∃ s ∈ S, ∃ q : G.Walk s w, q.length = ℓ ∧ ∀ y ∈ q.support, y ∉ P}
    with hDdef
  set W : Set (Fin n) := {w | (D w).Nonempty} with hWdef
  set h : Fin n → ℕ := fun w => sInf (D w) with hhdef
  -- Endpoints lie in the support.
  have end_mem : ∀ {u v : Fin n} (q : G.Walk u v), v ∈ q.support := by
    intro u v q
    induction q with
    | nil => simp [Walk.support_nil]
    | cons hq q' ih =>
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem _ ih
  -- Vertices of `S` avoid `P`.
  have hSP : ∀ w ∈ S, w ∉ P := by
    intro w hw hmem
    exact hdisj w hmem hw
  -- `h = 0` on `S` (the nil walk has length 0).
  have h0_all : ∀ w ∈ S, h w = 0 := by
    intro w hw
    have h0 : (0 : ℕ) ∈ D w := by
      simp only [hDdef, Set.mem_ofPred_eq]
      refine ⟨w, hw, Walk.nil, rfl, ?_⟩
      rw [Walk.support_nil]
      intro y hy
      have hyw : y = w := List.mem_singleton.mp hy
      rw [hyw]
      exact hSP w hw
    have hle : sInf (D w) ≤ 0 := Nat.sInf_le h0
    simp only [hhdef]
    exact Nat.le_zero.mp hle
  -- `h > 0` off `S` (a length-0 walk from `S` to `w` forces `w ∈ S`).
  have hpos_all : ∀ w ∈ W, w ∉ S → 0 < h w := by
    intro w hw hwS
    rcases Nat.eq_zero_or_pos (h w) with h0 | hpos
    · exfalso
      simp only [hWdef, Set.mem_ofPred_eq] at hw
      obtain ⟨ℓ, hℓ⟩ := hw
      simp only [hhdef] at h0
      have hmem : sInf (D w) ∈ D w := Nat.sInf_mem ⟨ℓ, hℓ⟩
      rw [h0] at hmem
      simp only [hDdef, Set.mem_ofPred_eq] at hmem
      obtain ⟨s, hsS, q, hqlen, _hqavoid⟩ := hmem
      have hseq : s = w := Walk.eq_of_length_eq_zero hqlen
      rw [hseq] at hsS
      exact hwS hsS
    · exact hpos
  refine ⟨W, h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `S ⊆ W`
    intro w hw
    simp only [hWdef, Set.mem_ofPred_eq]
    refine ⟨0, ?_⟩
    simp only [hDdef, Set.mem_ofPred_eq]
    refine ⟨w, hw, Walk.nil, rfl, ?_⟩
    rw [Walk.support_nil]
    intro y hy
    have hyw : y = w := List.mem_singleton.mp hy
    rw [hyw]
    exact hSP w hw
  · -- `W` avoids `P`
    intro w hw
    simp only [hWdef, Set.mem_ofPred_eq] at hw
    obtain ⟨ℓ, hℓ⟩ := hw
    simp only [hDdef, Set.mem_ofPred_eq] at hℓ
    obtain ⟨s, _hsS, q, _hqlen, hqavoid⟩ := hℓ
    exact hqavoid w (end_mem q)
  · -- `h = 0` on `S`
    exact h0_all
  · -- `h > 0` off `S`
    exact hpos_all
  · -- Parent property: predecessor on a shortest walk.
    intro w hw hwS
    have hw' : (D w).Nonempty := by
      simp only [hWdef, Set.mem_ofPred_eq] at hw
      exact hw
    have hmem : sInf (D w) ∈ D w := Nat.sInf_mem hw'
    simp only [hDdef, Set.mem_ofPred_eq] at hmem
    obtain ⟨s, hsS, q, hqlen, hqavoid⟩ := hmem
    have hpos : 0 < h w := hpos_all w (by simp only [hWdef, Set.mem_ofPred_eq]; exact hw') hwS
    have hqpos : 0 < q.length := by
      have hqw : q.length = h w := by
        simp only [hhdef]
        exact hqlen
      omega
    have hqnil : ¬ q.Nil := Walk.not_nil_iff_lt_length.mpr hqpos
    have hadj : G.Adj q.penultimate w := Walk.adj_penultimate hqnil
    -- `q.length - 1 ∈ D (penultimate)`, via `q.dropLast`.
    have hzmem : q.length - 1 ∈ D q.penultimate := by
      simp only [hDdef, Set.mem_ofPred_eq]
      refine ⟨s, hsS, q.dropLast, Walk.length_dropLast q, ?_⟩
      intro y hy
      rw [Walk.support_dropLast hqnil] at hy
      exact hqavoid y (mem_of_mem_dropLast _ _ hy)
    have hzW : q.penultimate ∈ W := by
      simp only [hWdef, Set.mem_ofPred_eq]
      exact ⟨q.length - 1, hzmem⟩
    -- Goal in `sInf` form.
    simp only [hhdef]
    refine ⟨q.penultimate, hzW, hadj, ?_⟩
    have hzle : sInf (D q.penultimate) ≤ q.length - 1 := Nat.sInf_le hzmem
    -- `h w ≤ h z + 1`: concat a shortest walk to `z` with the last edge.
    have hwle : sInf (D w) ≤ sInf (D q.penultimate) + 1 := by
      have hzmem' : sInf (D q.penultimate) ∈ D q.penultimate := Nat.sInf_mem ⟨_, hzmem⟩
      simp only [hDdef, Set.mem_ofPred_eq] at hzmem'
      obtain ⟨s₂, hs₂S, q₂, hq₂len, hq₂avoid⟩ := hzmem'
      have hconcat_avoid : ∀ y ∈ (q₂.concat hadj).support, y ∉ P := by
        intro y hy
        rw [Walk.support_concat] at hy
        rcases List.mem_append.mp hy with hleft | hright
        · exact hq₂avoid y hleft
        · have hyw : y = w := List.mem_singleton.mp hright
          rw [hyw]
          have hwP : w ∉ P := by
            have : w ∈ W := by
              simp only [hWdef, Set.mem_ofPred_eq]
              exact hw'
            have h1 : ∀ v ∈ W, v ∉ P := by
              intro v hv
              simp only [hWdef, Set.mem_ofPred_eq] at hv
              obtain ⟨ℓ, hℓ⟩ := hv
              simp only [hDdef, Set.mem_ofPred_eq] at hℓ
              obtain ⟨sv, _hsv, qv, _hqv, hqvavoid⟩ := hℓ
              exact hqvavoid v (end_mem qv)
            exact h1 w this
          exact hwP
      have h1 : sInf (D w) ≤ (q₂.concat hadj).length :=
        Nat.sInf_le ⟨s₂, hs₂S, q₂.concat hadj, rfl, hconcat_avoid⟩
      have h2 : (q₂.concat hadj).length = q₂.length + 1 :=
        Walk.length_concat q₂ hadj
      calc sInf (D w) ≤ (q₂.concat hadj).length := h1
        _ = q₂.length + 1 := h2
        _ = sInf (D q.penultimate) + 1 := by rw [hq₂len]
    have hge : sInf (D q.penultimate) + 1 ≤ sInf (D w) := by
      rw [← hqlen]
      omega
    exact le_antisymm hge hwle
  · -- `W` characterization.
    intro w
    constructor
    · intro hw
      simp only [hWdef, Set.mem_ofPred_eq] at hw
      obtain ⟨ℓ, hℓ⟩ := hw
      simp only [hDdef, Set.mem_ofPred_eq] at hℓ
      obtain ⟨s, hsS, q, _hqlen, hqavoid⟩ := hℓ
      refine ⟨hqavoid w (end_mem q), s, hsS, q, hqavoid⟩
    · rintro ⟨hwP, s, hsS, q, hqavoid⟩
      simp only [hWdef, Set.mem_ofPred_eq]
      refine ⟨q.length, ?_⟩
      simp only [hDdef, Set.mem_ofPred_eq]
      exact ⟨s, hsS, q, rfl, hqavoid⟩
  · -- Minimality.
    intro w _hw s hsS q hqavoid
    simp only [hhdef]
    exact Nat.sInf_le ⟨s, hsS, q, rfl, hqavoid⟩


/-
ASSEMBLY — proved for real from A2 (+ proved B2).
Target type copied verbatim from the platform record for
`CycleLengthsExp.ManyLengths.tree_extension_attach`.

Attachment argument (no induction on the walk): for `x ∈ X₀`, let `q` be
its connecting path from `s ∈ S` (length `≤ k`, internals avoiding
`S ∪ P.support`). The penultimate vertex `z` of `q` is adjacent to `x`
(`Walk.adj_penultimate`); `z` lies in `W` (the `q.dropLast` path avoids
`P`, by the `X₀` dropLast-condition plus `dropLast_head`), with
`h z ≤ q.length - 1 ≤ k - 1` (B2 minimality). If `z ∈ S`, its `T₁`-level
equals its `T`-level, which is in `[m-1, m]` by `hTfront`/`hTlev`. If
`z ∉ S`, its `T₁`-level is `level_T (r z) + h z` with
`level_T (r z) ∈ [m-1, m]` (A2 frontier-neighbour + `hTfront`/`hTlev`)
and `1 ≤ h z ≤ k - 1`, so the level is in `[m, m+k-1]`. Either way the
level lies in the `k+1` values `[m-1, m+k-1]`; pigeonhole over those
levels gives `j` and `X₁` with `|X₁| ≥ |X₀|/(k+1)` attached to level `j`.
`M₁` is the max `T₁`-level over the finite set `W`.
-/
theorem tree_extension_attach_proof (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G)
    (S : Set (Fin n)) (T : G.Subgraph) (v₀ : Fin n) (m : ℕ)
    (hScard : S.ncard = Nat.floor (α * (n : ℝ) / 4))
    (hTverts : T.verts = S)
    (hv₀ : v₀ ∈ S)
    (hTacyc : T.spanningCoe.IsAcyclic)
    (hTreach : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v)
    (hTlev : ∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v ≤ m)
    (hTmax : ∃ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = m)
    (hTfront : ∀ t ∈ S, ∀ q : Fin n, q ∉ S → G.Adj t q →
      m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀ t)
    (u v : Fin n) (P : G.Walk u v) (hPpath : P.IsPath)
    (hPlen : P.length = Nat.ceil (α * (n : ℝ) / 4) - 1)
    (hPdisj : ∀ w ∈ P.support, w ∉ S) :
    ∃ (T₁ : G.Subgraph) (M₁ : ℕ) (X₁ : Set (Fin n)) (j : ℕ),
      (T.verts ⊆ T₁.verts ∧
        (∀ a b : Fin n, T.spanningCoe.Adj a b → T₁.spanningCoe.Adj a b)) ∧
      T₁.spanningCoe.IsAcyclic ∧
      (∀ w ∈ T₁.verts, T₁.spanningCoe.Reachable v₀ w) ∧
      (∀ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w ≤ M₁) ∧
      (∃ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w = M₁) ∧
      (∀ w ∈ T₁.verts, w ∉ P.support) ∧
      X₁ ⊆ CycleLengthsExp.ManyLengths.X0 α G S P ∧
      ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
          ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) ≤ (X₁.ncard : ℝ) ∧
      (∀ x ∈ X₁, ∃ y ∈ T₁.verts,
        CycleLengthsExp.WellSpread.level T₁ v₀ y = j ∧ G.Adj x y) := by
  classical
  set k := CycleLengthsExp.ManyLengths.kNum α with hkdef
  -- `k ≥ 2` from `kNum α = 2 * ⌈R⌉₊ + 1` with `R > 0`.
  have hk2 : 2 ≤ k := by
    have hR : (0 : ℝ) < Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2) := by
      apply div_pos
      · exact Real.logb_pos (by norm_num) (by
          have h3 : (1 : ℝ) * α < 3 := by linarith [hα1]
          rwa [lt_div_iff₀ hα0])
      · exact Real.logb_pos (by norm_num) (by linarith [hα0])
    have hceil : 1 ≤ Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) :=
      Nat.ceil_pos.mpr hR
    have hkexp : CycleLengthsExp.ManyLengths.kNum α =
        2 * Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 1 := rfl
    rw [hkdef, hkexp]
    omega
  -- `m ≥ 1` from `hTmax` (levels are `dist + 1 ≥ 1`).
  obtain ⟨vm, hvmS, hvmlev⟩ := hTmax
  have hm1 : 1 ≤ m := by
    have h1 : 1 ≤ CycleLengthsExp.WellSpread.level T v₀ vm := by
      show 1 ≤ T.spanningCoe.dist v₀ vm + 1
      omega
    omega
  -- Deep input B2: distance to `S` avoiding `P.support`.
  obtain ⟨W, h, hSW, hWP, hhS, hhW, hparent, hWiff, hmin⟩ :=
    dist_avoid_pred_ax n G S {w | w ∈ P.support} (by
      intro w hw
      exact hPdisj w hw)
  -- Deep input A2: extension parent tree.
  obtain ⟨T₁, r, hT₁verts, hText, hT₁acyc, hT₁reach, hrW, hrS, hdist, hrfront⟩ :=
    ext_parent_tree_ax G S T v₀ hTverts hv₀ hTacyc hTreach W hSW h hhS hhW hparent
  -- Level formula in `T₁`.
  have hlevel : ∀ w ∈ W,
      CycleLengthsExp.WellSpread.level T₁ v₀ w =
        CycleLengthsExp.WellSpread.level T v₀ (r w) + h w := by
    intro w hw
    show T₁.spanningCoe.dist v₀ w + 1 = T.spanningCoe.dist v₀ (r w) + 1 + h w
    rw [hdist w hw]
    omega
  -- Attachment: every `x ∈ X₀` has a neighbour in `T₁` at a level in
  -- `[m-1, m+k-1]`, namely the penultimate vertex of its connecting path.
  have hattach_all : ∀ x ∈ CycleLengthsExp.ManyLengths.X0 α G S P,
      ∃ y ∈ T₁.verts,
        CycleLengthsExp.WellSpread.level T₁ v₀ y ∈ Finset.Icc (m - 1) (m + k - 1) ∧
        G.Adj x y := by
    intro x hx
    simp only [CycleLengthsExp.ManyLengths.X0, Set.mem_ofPred_eq] at hx
    obtain ⟨hxP, s, hsS, q, _hqpath, hqlen, hqavoid⟩ := hx
    rw [← hkdef] at hqlen
    cases q with
    | nil => exact absurd hsS (hPdisj x hxP)
    | cons hq q' =>
      have hqnil : ¬ (Walk.cons hq q').Nil :=
        Walk.not_nil_iff_lt_length.mpr (by rw [Walk.length_cons]; omega)
      have hadj : G.Adj (Walk.cons hq q').penultimate x :=
        Walk.adj_penultimate hqnil
      have hsupp : (Walk.cons hq q').support = s :: q'.support :=
        Walk.support_cons hq q'
      have hzP : (Walk.cons hq q').penultimate ∉ P.support := by
        have hmem : (Walk.cons hq q').penultimate ∈
            (Walk.cons hq q').support.dropLast :=
          Walk.penultimate_mem_dropLast_support hqnil
        rw [hsupp] at hmem
        rcases dropLast_head s q'.support (Walk.cons hq q').penultimate hmem with
          hleft | hright
        · have hzcond := hqavoid (Walk.cons hq q').penultimate
            (by rw [hsupp]; exact hleft)
          exact hzcond.2
        · rw [hright]
          exact fun hmem2 => hPdisj s hmem2 hsS
      have hdrop_avoid :
          ∀ y ∈ (Walk.cons hq q').dropLast.support,
            y ∉ {w | w ∈ P.support} := by
        intro y hy
        rw [Walk.support_dropLast hqnil, hsupp] at hy
        rcases dropLast_head s q'.support y hy with hleft | hright
        · have hycond := hqavoid y (by rw [hsupp]; exact hleft)
          exact fun hmem2 => hycond.2 hmem2
        · rw [hright]
          exact fun hmem2 => hPdisj s hmem2 hsS
      have hzW : (Walk.cons hq q').penultimate ∈ W := by
        apply (hWiff _).mpr
        refine ⟨?_, s, hsS, (Walk.cons hq q').dropLast, hdrop_avoid⟩
        exact fun hmem2 => hzP hmem2
      have hzle : h (Walk.cons hq q').penultimate ≤ (Walk.cons hq q').length - 1 := by
        have hmin' := hmin _ hzW s hsS (Walk.cons hq q').dropLast hdrop_avoid
        rwa [Walk.length_dropLast] at hmin'
      by_cases hzS : (Walk.cons hq q').penultimate ∈ S
      · refine ⟨(Walk.cons hq q').penultimate, ?_, ?_, hadj.symm⟩
        · rw [hT₁verts]; exact hSW hzS
        · rw [Finset.mem_Icc]
          have hlev : CycleLengthsExp.WellSpread.level T₁ v₀
              (Walk.cons hq q').penultimate =
              CycleLengthsExp.WellSpread.level T v₀
                (Walk.cons hq q').penultimate := by
            rw [hlevel _ (hSW hzS), hrS _ hzS, hhS _ hzS, add_zero]
          rw [hlev]
          constructor
          · exact hTfront _ hzS x (fun hmem => hPdisj x hxP hmem) hadj
          · exact le_trans (hTlev _ hzS) (by omega)
      · have hzpos : 0 < h (Walk.cons hq q').penultimate := hhW _ hzW hzS
        refine ⟨(Walk.cons hq q').penultimate, ?_, ?_, hadj.symm⟩
        · rw [hT₁verts]; exact hzW
        · rw [Finset.mem_Icc]
          have hlev : CycleLengthsExp.WellSpread.level T₁ v₀
              (Walk.cons hq q').penultimate =
              CycleLengthsExp.WellSpread.level T v₀
                (r (Walk.cons hq q').penultimate) +
                h (Walk.cons hq q').penultimate := hlevel _ hzW
          rw [hlev]
          have hrS' : r (Walk.cons hq q').penultimate ∈ S := hrW _ hzW
          have hlow : m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀
              (r (Walk.cons hq q').penultimate) := by
            obtain ⟨w, hwS, hwAdj⟩ := hrfront _ hzW hzS
            exact hTfront _ hrS' w hwS hwAdj
          have hhigh : CycleLengthsExp.WellSpread.level T v₀
              (r (Walk.cons hq q').penultimate) ≤ m := hTlev _ hrS'
          omega
  -- `M₁`: the max `T₁`-level over the finite set `W`.
  have hWne : W.toFinset.Nonempty := ⟨v₀, by simpa using hSW hv₀⟩
  obtain ⟨wstar, hwstar_mem, hwstar_max⟩ :=
    Finset.exists_max_image W.toFinset
      (fun w => CycleLengthsExp.WellSpread.level T₁ v₀ w) hWne
  -- Choice of attachment vertex for each `x ∈ X₀` (total function).
  set y : Fin n → Fin n := fun x =>
    if hx : x ∈ CycleLengthsExp.ManyLengths.X0 α G S P then
      Classical.choose (hattach_all x hx) else v₀ with hydef
  have hy : ∀ x, x ∈ CycleLengthsExp.ManyLengths.X0 α G S P →
      y x ∈ T₁.verts ∧
        CycleLengthsExp.WellSpread.level T₁ v₀ (y x) ∈ Finset.Icc (m - 1) (m + k - 1) ∧
        G.Adj x (y x) := by
    intro x hx
    have h1 : y x = Classical.choose (hattach_all x hx) := by
      simp only [hydef, dif_pos hx]
    rw [h1]
    exact Classical.choose_spec (hattach_all x hx)
  set a : Fin n → ℕ := fun x => CycleLengthsExp.WellSpread.level T₁ v₀ (y x) with hadef
  have ha_eq : ∀ x, a x = CycleLengthsExp.WellSpread.level T₁ v₀ (y x) := by
    intro x
    rw [hadef]
  have ha_mem : ∀ x ∈ (CycleLengthsExp.ManyLengths.X0 α G S P).toFinset,
      a x ∈ Finset.Icc (m - 1) (m + k - 1) := by
    intro x hx
    have hx0 : x ∈ CycleLengthsExp.ManyLengths.X0 α G S P :=
      Set.mem_toFinset.mp hx
    rw [ha_eq]
    exact (hy x hx0).2.1
  -- Pigeonhole: some level `j` carries `≥ |X₀|/(k+1)` of `X₀`.
  have hIcc_card : (Finset.Icc (m - 1) (m + k - 1)).card = k + 1 := by
    rw [Nat.card_Icc]
    omega
  have hsum : (CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.card =
      ∑ j ∈ Finset.Icc (m - 1) (m + k - 1),
        (((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.filter
          (fun x => a x = j)).card) :=
    Finset.card_eq_sum_card_fiberwise ha_mem
  obtain ⟨j, hj⟩ : ∃ j,
      ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) / ((k : ℝ) + 1) ≤
        ((((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.filter
          (fun x => a x = j)).card : ℕ) : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hFcard : (((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.card : ℕ) : ℝ) =
        ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) := by
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hsumR : (∑ j ∈ Finset.Icc (m - 1) (m + k - 1),
        ((((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.filter
          (fun x => a x = j)).card : ℕ) : ℝ)) =
        (((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.card : ℕ) : ℝ) := by
      simp only [← Nat.cast_sum, hsum]
    have hlt : (∑ j ∈ Finset.Icc (m - 1) (m + k - 1),
        ((((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.filter
          (fun x => a x = j)).card : ℕ) : ℝ)) <
        ∑ j ∈ Finset.Icc (m - 1) (m + k - 1),
          ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) / ((k : ℝ) + 1) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.nonempty_Icc.mpr (by omega)
      · intro j _
        exact hcon j
    rw [Finset.sum_const, hIcc_card, nsmul_eq_mul] at hlt
    push_cast at hlt
    rw [hsumR, hFcard] at hlt
    have hk1ne : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hmul : ((k : ℝ) + 1) *
        (((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) / ((k : ℝ) + 1)) =
        ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) := by
      field_simp
    rw [hmul] at hlt
    exact lt_irrefl _ hlt
  -- Assemble the existential.
  refine ⟨T₁, CycleLengthsExp.WellSpread.level T₁ v₀ wstar,
    ↑(((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset).filter
      (fun x => a x = j)), j,
    ⟨?_, ?_⟩, hT₁acyc, (by rw [hT₁verts]; exact hT₁reach), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTverts, hT₁verts]; exact hSW
  · exact hText
  · intro w hw
    rw [hT₁verts] at hw
    apply hwstar_max
    simpa using hw
  · exact ⟨wstar, by rw [hT₁verts]; simpa using hwstar_mem, rfl⟩
  · intro w hw
    rw [hT₁verts] at hw
    have hnot : w ∉ {w | w ∈ P.support} := hWP w hw
    intro hmem
    exact hnot hmem
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    exact Set.mem_toFinset.mp hx.1
  · have hconv : (↑(((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset).filter
        (fun x => a x = j)) : Set (Fin n)).ncard =
        (((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset).filter
          (fun x => a x = j)).card := by
      have h1 : (↑(((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset).filter
          (fun x => a x = j)) : Set (Fin n)).ncard =
          (Finset.finite_toSet (((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset).filter
            (fun x => a x = j))).toFinset.card :=
        Set.ncard_eq_toFinset_card _ (Finset.finite_toSet _)
      rw [h1, Finset.finite_toSet_toFinset]
    rw [hconv]
    exact hj
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    obtain ⟨hxF, hxj⟩ := hx
    have hx0 : x ∈ CycleLengthsExp.ManyLengths.X0 α G S P :=
      Set.mem_toFinset.mp hxF
    obtain ⟨hy1, _hIcc, hy3⟩ := hy x hx0
    refine ⟨y x, hy1, ?_, hy3⟩
    rw [← ha_eq]
    exact hxj

/-- REPAIRED 2026-10-18: the original `branch_cycles` (6f2911cf) is FALSE as stated
(pendant-vertex counterexample with X₁ = {0}; see `branch_cycles_counterexample.md`).
This version adds the hypothesis `hX₁card2 : 2 ≤ X₁.ncard`, which the paper's
pair-cycle argument needs (with |X₁| ≥ 2, both branching cases give |X₃| ≥ |X₁|/4
with genuine cycles; with |X₁| = 1 the conclusion can force a cycle at a degree-1
vertex, which does not exist). The assembly must discharge `2 ≤ X₁.ncard` by
raising n₀ (see triage report). Branching + cycles (Friedman–Krivelevich, p. 14: "Let T₂ be the tree
obtained by connecting each vertex in X₁ to one of its neighbors in the last
level of T₁. Let T₃ be the minimal subtree of T₂ containing X₁ and let v be
its root ... One of the branches contains at most half of the vertices of X₁,
denote this set by Y and let X₂ = X₁ ∖ Y ... at least half of the vertices of
X₂ appear on P on the same side of u ... Finally we construct a cycle C_w for
every w ∈ X₃ ... As the lengths of the cycles {C_w} are all distinct ...").

Why the lengths are distinct: every `w ∈ X₁` is a leaf of `T₂` attached to a
level-`j` vertex, so `dist_{T₃}(w, v) = j - depth(v)` is CONSTANT over
`w ∈ X₁`; `C_w` has length `dist(v,u) + dist_P(u,w) + dist_{T₃}(w,v) =
A + dist_P(u,w)` with `A` independent of `w`, and `w ↦ dist_P(u,w)` is
injective on `X₃` because all of `X₃` lies on the same side of `u` along the
path `P`. The statement packages exactly what the assembly consumes: the
cycles, the constant `A`, an injective length function `segLen`, and the
`|X₃| ≥ |X₁|/4` count. The `T₂`/`T₃`/branching machinery is internal to this
node's proof. This node is the last of the three-node decomposition of
`CycleLengthsExp.ManyLengths.theorem_2` (parent, Open): it consumes the
extended tree `T₁`, the set `X₁` and the level `j` of `tree_extension_attach`,
and its output (X₃, A, segLen) is exactly what the assembly counts to get
`Ω(α³/log(1/α))n` distinct cycle lengths. -/
theorem h42b_up {V : Type*} {G : SimpleGraph V} (par : V → V) (z : V) : ∀ t : ℕ,
    (∀ s < t, G.Adj (par^[s] z) (par^[s+1] z)) →
    ∃ q : G.Walk z (par^[t] z), q.length = t ∧
      q.support = (List.range (t+1)).map (fun s => par^[s] z) := by
  intro t
  induction t with
  | zero => intro _; exact ⟨SimpleGraph.Walk.nil, rfl, by simp⟩
  | succ t ih =>
    intro hadj
    obtain ⟨q, hq1, hq2⟩ := ih (fun s hs => hadj s (by omega))
    refine ⟨q.concat (hadj t (by omega)), ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_concat, hq1]
    · rw [SimpleGraph.Walk.support_concat, hq2, List.range_succ (n := t + 1),
        List.map_append]
      rfl

theorem h42_branching (n : ℕ) (G : SimpleGraph (Fin n))
    (T₁ : G.Subgraph) (v₀ : Fin n) (X₁ : Set (Fin n)) (j : ℕ)
    (y : ∀ (x : Fin n), x ∈ X₁ → Fin n)
    (hT₁acyc : T₁.spanningCoe.IsAcyclic)
    (hT₁reach : ∀ w ∈ T₁.verts, T₁.spanningCoe.Reachable v₀ w)
    (hv₀ : v₀ ∈ T₁.verts)
    (hX₁T₁ : ∀ x ∈ X₁, x ∉ T₁.verts)
    (hy : ∀ (x : Fin n) (hx : x ∈ X₁), y x hx ∈ T₁.verts ∧
      CycleLengthsExp.WellSpread.level T₁ v₀ (y x hx) = j ∧ G.Adj x (y x hx))
    (hX₁card2 : 2 ≤ X₁.ncard) :
    ∃ (d : ℕ) (Y : Set (Fin n)) (w₀ : Fin n),
      Y ⊆ X₁ ∧ w₀ ∈ Y ∧ (Y.ncard : ℝ) ≤ (X₁.ncard : ℝ) / 2 ∧
      (∀ w : Fin n, w ∈ X₁ ∧ w ∉ Y → ∃ q : G.Walk w w₀, q.IsPath ∧ q.length = 2 * d + 2 ∧
        (∀ z ∈ q.support, z = w ∨ z = w₀ ∨ z ∈ T₁.verts)) := by
  classical
  let D : Fin n → ℕ := fun z => T₁.spanningCoe.dist v₀ z
  have hpex : ∀ z, ∃ u, z ∈ T₁.verts → z ≠ v₀ → T₁.spanningCoe.Adj u z ∧ D u + 1 = D z := by
    intro z
    by_cases hz : z ∈ T₁.verts ∧ z ≠ v₀
    · obtain ⟨u, hu1, hu2⟩ := h42_pred (hT₁reach z hz.1) hz.2
      exact ⟨u, fun _ _ => ⟨hu1, hu2⟩⟩
    · exact ⟨z, fun a b => absurd ⟨a, b⟩ hz⟩
  choose par hpar using hpex
  have hit : ∀ s z, z ∈ T₁.verts → s ≤ D z → par^[s] z ∈ T₁.verts ∧ D (par^[s] z) + s = D z := by
    intro s
    induction s with
    | zero => intro z hz _; exact ⟨hz, by simp⟩
    | succ s ih =>
      intro z hz hs
      obtain ⟨h1, h2⟩ := ih z hz (by omega)
      have hne : par^[s] z ≠ v₀ := by
        intro he; rw [he] at h2; have : D v₀ = 0 := by simp [D]
        omega
      obtain ⟨h3, h4⟩ := hpar _ h1 hne
      rw [Function.iterate_succ_apply']
      exact ⟨T₁.edge_vert h3, by omega⟩
  have hstep : ∀ s z, z ∈ T₁.verts → s < D z → G.Adj (par^[s] z) (par^[s+1] z) := by
    intro s z hz hs
    obtain ⟨h1, h2⟩ := hit s z hz (by omega)
    have hne : par^[s] z ≠ v₀ := by
      intro he; rw [he] at h2; have : D v₀ = 0 := by simp [D]
      omega
    obtain ⟨h3, _⟩ := hpar _ h1 hne
    rw [Function.iterate_succ_apply']
    exact (T₁.adj_sub h3).symm
  have hD0 : ∀ z ∈ T₁.verts, D z = 0 → z = v₀ := fun z hz h0 =>
    (((hT₁reach z hz).dist_eq_zero_iff).mp h0).symm
  let L := j - 1
  let y' : Fin n → Fin n := fun x => if hx : x ∈ X₁ then y x hx else x
  have hy' : ∀ x ∈ X₁, y' x ∈ T₁.verts ∧ D (y' x) = L ∧ G.Adj x (y' x) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hy x hx
    simp only [y', dif_pos hx]
    refine ⟨h1, ?_, h3⟩
    simp only [CycleLengthsExp.WellSpread.level] at h2
    simp only [D, L]; omega
  let agree : ℕ → Prop := fun i => ∀ x ∈ X₁, ∀ x' ∈ X₁, par^[L - i] (y' x) = par^[L - i] (y' x')
  have hanc0 : ∀ x ∈ X₁, par^[L] (y' x) = v₀ := by
    intro x hx
    obtain ⟨h1, h2, _⟩ := hy' x hx
    obtain ⟨h3, h4⟩ := hit L (y' x) h1 (by omega)
    exact hD0 _ h3 (by omega)
  have hag0 : agree 0 := by
    intro x hx x' hx'; simp only [Nat.sub_zero]; rw [hanc0 x hx, hanc0 x' hx']
  let i := Nat.findGreatest agree L
  have hiL : i ≤ L := Nat.findGreatest_le L
  have hagi : agree i := Nat.findGreatest_spec (Nat.zero_le L) hag0
  let d := L - i
  let key : Fin n → Fin n := fun x => if i < L then par^[d - 1] (y' x) else x
  have hdist : ∃ a ∈ X₁, ∃ b ∈ X₁, key a ≠ key b := by
    by_cases hlt : i < L
    · by_contra hcon
      push Not at hcon
      have : agree (i + 1) := by
        intro x hx x' hx'
        have := hcon x hx x' hx'
        simp only [key, if_pos hlt] at this
        have e : L - (i + 1) = d - 1 := by omega
        rw [e]; exact this
      exact Nat.findGreatest_is_greatest (lt_add_one i) (by omega) this
    · obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite X₁)).mp (by omega)
      exact ⟨a, ha, b, hb, by simp only [key, if_neg hlt]; exact hab⟩
  let F : Fin n → Set (Fin n) := fun x => {x' | x' ∈ X₁ ∧ key x' = key x}
  have hFsub : ∀ x, F x ⊆ X₁ := fun x z hz => hz.1
  have hdist' := hdist
  obtain ⟨a0, ha0, _⟩ := hdist'
  obtain ⟨w₀, hw₀mem, hw₀min⟩ := (Set.toFinite X₁).toFinset.exists_min_image (fun x => (F x).ncard)
    ⟨a0, (Set.Finite.mem_toFinset _).mpr ha0⟩
  rw [Set.Finite.mem_toFinset] at hw₀mem
  have hw₀min' : ∀ x ∈ X₁, (F w₀).ncard ≤ (F x).ncard := fun x hx =>
    hw₀min x ((Set.Finite.mem_toFinset _).mpr hx)
  refine ⟨d, F w₀, w₀, hFsub w₀, ⟨hw₀mem, rfl⟩, ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := hdist
    obtain ⟨c, hc, hcne⟩ : ∃ c ∈ X₁, key c ≠ key w₀ := by
      by_cases h : key a = key w₀
      · exact ⟨b, hb, fun h' => hab (h.trans h'.symm)⟩
      · exact ⟨a, ha, h⟩
    have hdisj : Disjoint (F w₀) (F c) := by
      rw [Set.disjoint_left]; intro z hz1 hz2; exact hcne (hz2.2.symm.trans hz1.2)
    have h1 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    have h2 := Set.ncard_le_ncard (Set.union_subset (hFsub w₀) (hFsub c)) (Set.toFinite X₁)
    have h3 := hw₀min' c hc
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have : (F w₀).ncard * 2 ≤ X₁.ncard := by omega
    exact_mod_cast this
  · rintro w ⟨hw, hwY⟩
    have hkey : key w ≠ key w₀ := fun h => hwY ⟨hw, h⟩
    have hww₀ : w ≠ w₀ := fun h => hkey (by rw [h])
    obtain ⟨hyw1, hyw2, hyw3⟩ := hy' w hw
    obtain ⟨hyv1, hyv2, hyv3⟩ := hy' w₀ hw₀mem
    have e : par^[d] (y' w) = par^[d] (y' w₀) := hagi w hw w₀ hw₀mem
    have hchain : ∀ s s', s ≤ d → s' ≤ d → par^[s] (y' w) = par^[s'] (y' w₀) → s = d ∧ s' = d := by
      intro s s' hs hs' hss
      have h1 := (hit s (y' w) hyw1 (by omega)).2
      have h2 := (hit s' (y' w₀) hyv1 (by omega)).2
      rw [hss] at h1
      have hss' : s = s' := by omega
      subst hss'
      by_contra hcon
      have hsd : s < d := by omega
      have hlt : i < L := by omega
      apply hkey
      simp only [key, if_pos hlt]
      have e2 : d - 1 = (d - 1 - s) + s := by omega
      rw [e2, Function.iterate_add_apply, Function.iterate_add_apply, hss]
    have hinj : ∀ z, z ∈ T₁.verts → ∀ s ≤ D z, ∀ s' ≤ D z, par^[s] z = par^[s'] z → s = s' := by
      intro z hz s hs s' hs' h
      have h1 := (hit s z hz hs).2
      have h2 := (hit s' z hz hs').2
      rw [h] at h1; omega
    obtain ⟨qa, hqa1, hqa2⟩ := h42b_up par (y' w) d (fun s hs => hstep s (y' w) hyw1 (by omega))
    obtain ⟨qb, hqb1, hqb2⟩ := h42b_up par (y' w₀) d (fun s hs => hstep s (y' w₀) hyv1 (by omega))
    let A := (List.range (d+1)).map (fun s => par^[s] (y' w))
    let B := (List.range d).map (fun s => par^[s] (y' w₀))
    have hBtail : qb.support.reverse.tail = B.reverse := by
      rw [hqb2, List.tail_reverse, List.range_succ, List.map_append]
      simp [B]
    let full : G.Walk w w₀ :=
      (SimpleGraph.Walk.cons hyw3 (qa.append (qb.reverse.copy e.symm rfl))).concat hyv3.symm
    have hsup : full.support = (w :: (A ++ B.reverse)) ++ [w₀] := by
      simp only [full, SimpleGraph.Walk.support_concat, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_copy]
      rw [SimpleGraph.Walk.support_reverse, hBtail, hqa2]
    have memA : ∀ z ∈ A, ∃ s, s ≤ d ∧ par^[s] (y' w) = z := by
      intro z hz
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz
      exact ⟨s, by rw [List.mem_range] at hs; omega, rfl⟩
    have memB : ∀ z ∈ B.reverse, ∃ s, s < d ∧ par^[s] (y' w₀) = z := by
      intro z hz
      rw [List.mem_reverse] at hz
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz
      exact ⟨s, by rw [List.mem_range] at hs; omega, rfl⟩
    have hAT : ∀ z ∈ A, z ∈ T₁.verts := by
      intro z hz; obtain ⟨s, hs, rfl⟩ := memA z hz; exact (hit s _ hyw1 (by omega)).1
    have hBT : ∀ z ∈ B.reverse, z ∈ T₁.verts := by
      intro z hz; obtain ⟨s, hs, rfl⟩ := memB z hz; exact (hit s _ hyv1 (by omega)).1
    refine ⟨full, ?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def, hsup]
      rw [List.nodup_append, List.nodup_cons, List.nodup_append]
      refine ⟨⟨?_, ⟨?_, ?_, ?_⟩⟩, List.nodup_singleton _, ?_⟩
      · intro hmem
        rw [List.mem_append] at hmem
        rcases hmem with h | h
        · exact hX₁T₁ w hw (hAT w h)
        · exact hX₁T₁ w hw (hBT w h)
      · apply List.Nodup.map_on
        · intro s hs s' hs' h
          rw [List.mem_range] at hs hs'
          exact hinj _ hyw1 s (by omega) s' (by omega) h
        · exact List.nodup_range
      · rw [List.nodup_reverse]
        apply List.Nodup.map_on
        · intro s hs s' hs' h
          rw [List.mem_range] at hs hs'
          exact hinj _ hyv1 s (by omega) s' (by omega) h
        · exact List.nodup_range
      · intro a ha b hb hab
        obtain ⟨s, hs, rfl⟩ := memA a ha
        obtain ⟨s', hs', rfl⟩ := memB b hb
        have := hchain s s' hs (by omega) hab
        omega
      · intro a ha b hb hab
        rw [List.mem_singleton] at hb
        rw [hb] at hab
        rcases List.mem_cons.mp ha with h | h
        · exact hww₀ (h.symm.trans hab)
        · rw [List.mem_append] at h
          rcases h with h | h
          · exact hX₁T₁ w₀ hw₀mem (hab ▸ hAT a h)
          · exact hX₁T₁ w₀ hw₀mem (hab ▸ hBT a h)
    · simp only [full, SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy,
        SimpleGraph.Walk.length_reverse, hqa1, hqb1]
      omega
    · intro z hz
      rw [hsup] at hz
      rw [List.mem_append, List.mem_cons, List.mem_append, List.mem_singleton] at hz
      rcases hz with (h | h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (hAT z h))
      · exact Or.inr (Or.inr (hBT z h))
      · exact Or.inr (Or.inl h)

theorem cl_prefix_mem {α : Type*} [DecidableEq α] {l₁ l₂ : List α} (hp : l₁ <+: l₂) {a : α}
    (ha : a ∈ l₂) (hlt : l₂.idxOf a < l₁.length) : a ∈ l₁ ∧ l₁.idxOf a = l₂.idxOf a := by
  obtain ⟨t, rfl⟩ := hp
  by_cases h : a ∈ l₁
  · exact ⟨h, (List.idxOf_append_of_mem h).symm⟩
  · rw [List.idxOf_append_of_notMem h] at hlt; omega

theorem cl_seg {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (P : G.Walk u v) (hP : P.IsPath)
    (a b : Fin n) (ha : a ∈ P.support) (hb : b ∈ P.support)
    (hab : P.support.idxOf a ≤ P.support.idxOf b) :
    ∃ W : G.Walk a b, W.IsPath ∧ W.support ⊆ P.support ∧
      W.length = P.support.idxOf b - P.support.idxOf a := by
  have hpre := P.support_takeUntil_prefix_support hb
  have hlen : (P.takeUntil b hb).support.length = P.support.idxOf b + 1 := by
    rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_takeUntil]
  obtain ⟨ha', hidx⟩ := cl_prefix_mem hpre ha (by omega)
  refine ⟨(P.takeUntil b hb).dropUntil a ha', (hP.takeUntil hb).dropUntil ha', ?_, ?_⟩
  · intro x hx
    exact P.support_takeUntil_subset hb ((P.takeUntil b hb).support_dropUntil_subset ha' hx)
  · rw [SimpleGraph.Walk.length_dropUntil, SimpleGraph.Walk.length_takeUntil, hidx]

theorem h42c_ne_head {n : ℕ} {G : SimpleGraph (Fin n)} {u v x : Fin n} (p : G.Walk u v) (hp : p.IsPath)
    (hx : x ∈ p.support.tail) : x ≠ u := by
  have h := hp.support_nodup
  rw [SimpleGraph.Walk.support_eq_cons] at h
  intro hxu; subst hxu; exact (List.nodup_cons.mp h).1 hx

theorem h42c_cycle {n : ℕ} {G : SimpleGraph (Fin n)} {w w₀ : Fin n} (hne : w ≠ w₀)
    (leg : G.Walk w w₀) (seg : G.Walk w₀ w) (hl : leg.IsPath) (hs : seg.IsPath)
    (h2 : 2 ≤ leg.length)
    (hdisj : ∀ a ∈ leg.support.tail, ∀ b ∈ seg.support.tail, a ≠ b) : (leg.append seg).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  have hnn : ¬ (leg.append seg).Nil := by
    intro h; have := SimpleGraph.Walk.Nil.length_eq_zero h  
    rw [SimpleGraph.Walk.length_append] at this; omega
  have hseg1 : seg.length ≠ 0 := by
    intro h0; exact hne (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
  constructor
  · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_tail_of_not_nil _ hnn,
      SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_eq_cons leg, List.cons_append,
      List.tail_cons]
    rw [List.nodup_append]
    refine ⟨?_, ?_, hdisj⟩
    · exact hl.support_nodup.sublist (List.tail_sublist _)
    · exact hs.support_nodup.sublist (List.tail_sublist _)
  · rw [SimpleGraph.Walk.length_append]; omega

theorem branch_cycles_repaired_proof (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G)
    (S : Set (Fin n)) (T : G.Subgraph) (v₀ : Fin n) (m : ℕ)
    (hScard : S.ncard = Nat.floor (α * (n : ℝ) / 4))
    (hTverts : T.verts = S)
    (hv₀ : v₀ ∈ S)
    (hTacyc : T.spanningCoe.IsAcyclic)
    (hTreach : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v)
    (hTlev : ∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v ≤ m)
    (hTmax : ∃ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = m)
    (hTfront : ∀ t ∈ S, ∀ q : Fin n, q ∉ S → G.Adj t q →
      m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀ t)
    (u v : Fin n) (P : G.Walk u v) (hPpath : P.IsPath)
    (hPlen : P.length = Nat.ceil (α * (n : ℝ) / 4) - 1)
    (hPdisj : ∀ w ∈ P.support, w ∉ S)
    (T₁ : G.Subgraph) (M₁ : ℕ) (X₁ : Set (Fin n)) (j : ℕ)
    (hText : T.verts ⊆ T₁.verts ∧
      (∀ a b : Fin n, T.spanningCoe.Adj a b → T₁.spanningCoe.Adj a b))
    (hT₁acyc : T₁.spanningCoe.IsAcyclic)
    (hT₁reach : ∀ w ∈ T₁.verts, T₁.spanningCoe.Reachable v₀ w)
    (hT₁lev : ∀ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w ≤ M₁)
    (hT₁max : ∃ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w = M₁)
    (hT₁avoid : ∀ w ∈ T₁.verts, w ∉ P.support)
    (hX₁sub : X₁ ⊆ CycleLengthsExp.ManyLengths.X0 α G S P)
    (hX₁card : ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
        ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) ≤ (X₁.ncard : ℝ))
    (hX₁card2 : 2 ≤ X₁.ncard)
    (hattach : ∀ x ∈ X₁, ∃ y ∈ T₁.verts,
      CycleLengthsExp.WellSpread.level T₁ v₀ y = j ∧ G.Adj x y) :
    ∃ (X₃ : Set (Fin n)) (A : ℕ) (segLen : Fin n → ℕ),
      X₃ ⊆ X₁ ∧
      (X₁.ncard : ℝ) / 4 ≤ (X₃.ncard : ℝ) ∧
      (∀ w ∈ X₃, ∃ cyc : G.Walk w w, cyc.IsCycle ∧ cyc.length = A + segLen w) ∧
      Set.InjOn segLen X₃ := by
  classical
  have hX₁T₁ : ∀ x ∈ X₁, x ∉ T₁.verts := fun x hx hxT => hT₁avoid x hxT (hX₁sub hx).1
  have hv₀T₁ : v₀ ∈ T₁.verts := hText.1 (hTverts ▸ hv₀)
  choose yy hyy using hattach
  obtain ⟨d, Y, w₀, hYX, hw₀Y, hYcard, hlegs⟩ :=
    h42_branching n G T₁ v₀ X₁ j yy hT₁acyc hT₁reach hv₀T₁ hX₁T₁ hyy hX₁card2
  have hw₀X : w₀ ∈ X₁ := hYX hw₀Y
  have hPs : ∀ x ∈ X₁, x ∈ P.support := fun x hx => (hX₁sub hx).1
  have hseg : ∀ a b, a ∈ P.support → b ∈ P.support → ∃ W : G.Walk a b, W.IsPath ∧
      W.support ⊆ P.support ∧
      W.length = (if P.support.idxOf a ≤ P.support.idxOf b then
          P.support.idxOf b - P.support.idxOf a else
          P.support.idxOf a - P.support.idxOf b) := by
    intro a b ha hb
    by_cases h : P.support.idxOf a ≤ P.support.idxOf b
    · obtain ⟨W, h1, h2, h3⟩ := cl_seg P hPpath a b ha hb h
      exact ⟨W, h1, h2, by rw [if_pos h, h3]⟩
    · obtain ⟨W, h1, h2, h3⟩ := cl_seg P hPpath b a hb ha (by omega)
      refine ⟨W.reverse, h1.reverse, by rw [SimpleGraph.Walk.support_reverse]; intro x hx; exact h2 (List.mem_reverse.mp hx), ?_⟩
      rw [if_neg h, SimpleGraph.Walk.length_reverse, h3]
  let idx : Fin n → ℕ := fun x => P.support.idxOf x
  let segLen : Fin n → ℕ := fun w => if idx w₀ ≤ idx w then idx w - idx w₀ else idx w₀ - idx w
  have hcyc : ∀ w, w ∈ X₁ → w ∉ Y → ∃ cyc : G.Walk w w, cyc.IsCycle ∧ cyc.length = (2 * d + 2) + segLen w := by
    intro w hw hwY
    have hne : w ≠ w₀ := fun h => hwY (h ▸ hw₀Y)
    obtain ⟨leg, hlp, hll, hls⟩ := hlegs w ⟨hw, hwY⟩
    obtain ⟨seg, hsp, hss, hsl⟩ := hseg w₀ w (hPs w₀ hw₀X) (hPs w hw)
    refine ⟨leg.append seg, h42c_cycle hne leg seg hlp hsp (by omega) ?_, ?_⟩
    · intro a ha b hb hab
      subst hab
      have h1 := h42c_ne_head leg hlp ha
      have h2 := h42c_ne_head seg hsp hb
      have h3 : a ∈ P.support := hss (List.mem_of_mem_tail hb)
      rcases hls a (List.mem_of_mem_tail ha) with h | h | h
      · exact h1 h
      · exact h2 h
      · exact hT₁avoid a h h3
    · rw [SimpleGraph.Walk.length_append, hll, hsl]
  have hidx_inj : ∀ a ∈ X₁, ∀ b ∈ X₁, idx a = idx b → a = b := fun a ha b _ h =>
    (List.idxOf_inj (hPs a ha)).mp h
  let X₂ : Set (Fin n) := X₁ \ Y
  let Lft : Set (Fin n) := {w | w ∈ X₂ ∧ idx w < idx w₀}
  let Rgt : Set (Fin n) := {w | w ∈ X₂ ∧ idx w₀ < idx w}
  have hsplit : X₂ ⊆ Lft ∪ Rgt := by
    intro w hw
    have hne : w ≠ w₀ := fun h => hw.2 (h ▸ hw₀Y)
    have hne' : idx w ≠ idx w₀ := fun h => hne (hidx_inj w hw.1 w₀ hw₀X h)
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, h⟩
  have hc1 : X₂.ncard ≤ Lft.ncard + Rgt.ncard :=
    (Set.ncard_le_ncard hsplit (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  have hc2 : X₂.ncard + Y.ncard = X₁.ncard := Set.ncard_diff_add_ncard_of_subset hYX (Set.toFinite _)
  have hc3 : 2 * Y.ncard ≤ X₁.ncard := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)] at hYcard
    have : (Y.ncard * 2 : ℕ) ≤ X₁.ncard := by exact_mod_cast hYcard
    omega
  have hfin : ∀ X₃ : Set (Fin n), X₃ ⊆ X₂ → X₁.ncard ≤ X₃.ncard * 4 → Set.InjOn segLen X₃ →
      ∃ (X₃ : Set (Fin n)) (A : ℕ) (segLen : Fin n → ℕ),
      X₃ ⊆ X₁ ∧ (X₁.ncard : ℝ) / 4 ≤ (X₃.ncard : ℝ) ∧
      (∀ w ∈ X₃, ∃ cyc : G.Walk w w, cyc.IsCycle ∧ cyc.length = A + segLen w) ∧
      Set.InjOn segLen X₃ := by
    intro X₃ hX₃ hcard hinj
    refine ⟨X₃, 2 * d + 2, segLen, fun w hw => (hX₃ hw).1, ?_, fun w hw => hcyc w (hX₃ hw).1 (hX₃ hw).2, hinj⟩
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
    exact_mod_cast hcard
  by_cases hcmp : Lft.ncard ≤ Rgt.ncard
  · refine hfin Rgt (fun w hw => hw.1) (by omega) ?_
    intro a ha b hb hab
    have h1 := ha.2; have h2 := hb.2
    simp only [segLen] at hab
    rw [if_pos h1.le, if_pos h2.le] at hab
    exact hidx_inj a ha.1.1 b hb.1.1 (by omega)
  · refine hfin Lft (fun w hw => hw.1) (by omega) ?_
    intro a ha b hb hab
    have h1 := ha.2; have h2 := hb.2
    simp only [segLen] at hab
    rw [if_neg (by omega), if_neg (by omega)] at hab
    exact hidx_inj a ha.1.1 b hb.1.1 (by omega)



theorem solution : ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      CycleLengthsExp.WellSpread.IsAlphaExpander α G →
        c * (α ^ 3 / Real.logb 2 (2 / α)) * (n : ℝ) ≤
          ((CycleLengthsExp.WellSpread.cycleLengths G).ncard : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := k_bound_proof
  refine ⟨1 / (48 * (K + 1)), by positivity, fun α hα0 hα1 => ?_⟩
  refine ⟨Nat.ceil (12 / α) + Nat.ceil (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3) + 1, fun n hn G hG => ?_⟩
  -- `n ≥ 1` and `12 ≤ α * n` from `n ≥ ⌈12/α⌉₊ + 1`.
  have hn1 : 1 ≤ n := by omega
  have hαn : (12 : ℝ) ≤ α * (n : ℝ) := by
    have h1 : (12 : ℝ) / α ≤ (Nat.ceil (12 / α) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (12 / α) : ℝ)) + 1 ≤ (n : ℝ) := by
      have hnA : Nat.ceil (12 / α) + 1 ≤ n := by omega
      exact_mod_cast hnA
    have h3 : (12 : ℝ) / α < (n : ℝ) := by linarith
    rw [div_lt_iff₀ hα0] at h3
    rw [mul_comm] at h3
    linarith
  -- BFS tree prefix (NEW NODE 1).
  obtain ⟨S, T, v₀, m, hScard, hTverts, hv₀, hTacyc, hTreach, hTlev, hTmax, hTfront⟩ :=
    bfs_tree_prefix_proof n α hα0 hα1 hαn G hG
  -- Long path `P` in `G ∖ S` (proved child).
  obtain ⟨u, v, P, hPpath, hPlen, hPdisj⟩ :=
    path_after_deletion_proof n (by omega) α hα0 hα1 G hG S hScard
  -- `|X₀| ≥ α²n/12` (proved child).
  have hX0 := x0_large_proof n α hα0 hα1 hαn G hG S hScard u v P hPpath hPlen hPdisj
  -- Tree extension + attachment pigeonhole (NEW NODE 2).
  obtain ⟨T₁, M₁, X₁, j, hText, hT₁acyc, hT₁reach, hT₁lev, hT₁max, hT₁avoid,
    hX₁sub, hX₁card, hattach⟩ :=
    tree_extension_attach_proof n α hα0 hα1 G hG S T v₀ m hScard hTverts hv₀ hTacyc
      hTreach hTlev hTmax hTfront u v P hPpath hPlen hPdisj
  -- Real facts moved up: needed to discharge `2 ≤ X₁.ncard` for the repaired node.
  have hL1 : (1 : ℝ) ≤ Real.logb 2 (2 / α) := by
    have h2 : (2 : ℝ) ≤ 2 / α := by
      rw [le_div_iff₀ hα0]
      linarith [hα1]
    calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (2 / α) :=
        Real.logb_le_logb_of_le (show (1 : ℝ) < 2 by norm_num)
          (show (0 : ℝ) < 2 by norm_num) h2
  have hLpos : (0 : ℝ) < Real.logb 2 (2 / α) := by linarith [hL1]
  have hLne : Real.logb 2 (2 / α) ≠ 0 := ne_of_gt hLpos
  have hαne : α ≠ 0 := ne_of_gt hα0
  have hK1pos : (0 : ℝ) < K + 1 := by linarith [hK0]
  have hK1ne : K + 1 ≠ 0 := ne_of_gt hK1pos
  have hLα : (1 : ℝ) ≤ Real.logb 2 (2 / α) / α := by
    rw [le_div_iff₀ hα0]
    calc (1 : ℝ) * α = α := one_mul _
      _ ≤ 1 := hα1
      _ ≤ Real.logb 2 (2 / α) := hL1
  have hk1 : (CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1 ≤
      (K + 1) * Real.logb 2 (2 / α) / α := by
    have hk := hK α hα0 hα1
    calc (CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1
        ≤ K * Real.logb 2 (2 / α) / α + Real.logb 2 (2 / α) / α := by linarith
      _ = (K + 1) * Real.logb 2 (2 / α) / α := by ring
  have hk1pos : (0 : ℝ) < (CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1 := by positivity
  -- Discharge `2 ≤ X₁.ncard`: |X₀|/(k+1) ≥ 2 via n ≥ 24(K+1)L/α³.
  have hn_big : (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3 : ℝ) ≤ (n : ℝ) := by
    have h1 : (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3 : ℝ) ≤
        (Nat.ceil (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3) : ℝ) ≤ (n : ℝ) := by
      have hnB : Nat.ceil (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3) ≤ n := by omega
      exact_mod_cast hnB
    linarith
  have hα3 : (24 : ℝ) * (K + 1) * Real.logb 2 (2 / α) ≤ α ^ 3 * (n : ℝ) := by
    have hα3pos : (0 : ℝ) < α ^ 3 := by positivity
    rw [div_le_iff₀ hα3pos] at hn_big
    linarith [hn_big]
  have hkey : (2 : ℝ) * ((K + 1) * Real.logb 2 (2 / α) / α) ≤ α ^ 2 * (n : ℝ) / 12 := by
    have h1 : (2 : ℝ) * ((K + 1) * Real.logb 2 (2 / α) / α) =
        (24 * (K + 1) * Real.logb 2 (2 / α)) / (12 * α) := by
      field_simp
      ring
    rw [h1, div_le_div_iff₀ (by positivity : (0 : ℝ) < 12 * α) (by norm_num : (0 : ℝ) < 12)]
    nlinarith [hα3]
  have hX0div : (2 : ℝ) ≤ ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
      ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) := by
    rw [le_div_iff₀ hk1pos]
    calc (2 : ℝ) * ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1)
        ≤ 2 * ((K + 1) * Real.logb 2 (2 / α) / α) :=
          mul_le_mul_of_nonneg_left hk1 (by norm_num)
      _ ≤ α ^ 2 * (n : ℝ) / 12 := hkey
      _ ≤ ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) := hX0
  have hX₁card2 : 2 ≤ X₁.ncard := by
    have h : (2 : ℝ) ≤ (X₁.ncard : ℝ) := le_trans hX0div hX₁card
    exact_mod_cast h
  -- Branching + cycles (NEW NODE 3).
  obtain ⟨X₃, A, segLen, hX₃sub, hX₃card, hcyc, hinj⟩ :=
    branch_cycles_repaired_proof n α hα0 hα1 G hG S T v₀ m hScard hTverts hv₀ hTacyc
      hTreach hTlev hTmax hTfront u v P hPpath hPlen hPdisj
      T₁ M₁ X₁ j hText hT₁acyc hT₁reach hT₁lev hT₁max hT₁avoid hX₁sub hX₁card hX₁card2 hattach
  -- Counting: the cycle lengths `A + segLen w`, `w ∈ X₃`, are distinct
  -- members of `cycleLengths G`, so `|X₃| ≤ |cycleLengths G|`.
  have himg : (fun w => A + segLen w) '' X₃ ⊆
      CycleLengthsExp.WellSpread.cycleLengths G := by
    rintro ℓ ⟨w, hw, rfl⟩
    obtain ⟨cyc, hcyc', hlen⟩ := hcyc w hw
    exact ⟨w, cyc, hcyc', hlen⟩
  have hinj' : Set.InjOn (fun w => A + segLen w) X₃ := by
    intro a ha b hb h
    exact hinj ha hb (Nat.add_left_cancel h)
  have himgcard : ((fun w => A + segLen w) '' X₃).ncard = X₃.ncard :=
    hinj'.ncard_image
  -- `cycleLengths G` is finite: a cycle has length `≤ n`.
  have hfin : (CycleLengthsExp.WellSpread.cycleLengths G).Finite := by
    apply Set.Finite.subset (Set.finite_le_nat n)
    rintro ℓ ⟨w, p, hp, rfl⟩
    have hnod := hp.support_nodup
    have h1 : p.support.tail.toFinset.card ≤ Finset.univ.card := Finset.card_le_univ _
    rw [List.toFinset_card_of_nodup hnod, Finset.card_univ, Fintype.card_fin] at h1
    have h2 : p.support.tail.length = p.support.length - 1 := List.length_tail
    have h3 : p.support.length = p.length + 1 := p.length_support
    simp only [Set.mem_ofPred_eq]
    omega
  have hle1 : X₃.ncard ≤ (CycleLengthsExp.WellSpread.cycleLengths G).ncard := by
    rw [← himgcard]
    exact Set.ncard_le_ncard himg hfin
  have hle1R : (X₃.ncard : ℝ) ≤
      ((CycleLengthsExp.WellSpread.cycleLengths G).ncard : ℝ) := by
    exact_mod_cast hle1
  -- Real arithmetic: `|X₃| ≥ α²n / (48(k+1))` and `k+1 ≤ (K+1)·L/α`.
  have hX3 : α ^ 2 * (n : ℝ) / (48 * ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1)) ≤
      (X₃.ncard : ℝ) := by
    have hC : ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
        (((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) * 4) ≤ (X₃.ncard : ℝ) := by
      have h1 := div_le_div_of_nonneg_right hX₁card (show (0 : ℝ) ≤ 4 by norm_num)
      rw [div_div] at h1
      linarith [hX₃card]
    have hD : α ^ 2 * (n : ℝ) / 12 /
        (((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) * 4) ≤
        ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
          (((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) * 4) :=
      div_le_div_of_nonneg_right hX0 (by positivity)
    have heq : α ^ 2 * (n : ℝ) / 12 /
        (((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) * 4) =
        α ^ 2 * (n : ℝ) / (48 * ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1)) := by
      rw [div_div]
      congr 1
      ring
    rw [heq] at hD
    linarith [hC, hD]
  -- Real arithmetic: `|X₃| ≥ α²n / (48(k+1))` and `k+1 ≤ (K+1)·L/α`.
  -- (Flattened to solution level: nested `have`s inside the old `hgoal`
  -- block repeatedly broke the parser in elab rounds 1–3.)
  have heq2 : (1 / (48 * (K + 1))) * (α ^ 3 / Real.logb 2 (2 / α)) * (n : ℝ) =
      α ^ 2 * (n : ℝ) / (48 * ((K + 1) * Real.logb 2 (2 / α) / α)) := by
    field_simp
  have hcmp2 : α ^ 2 * (n : ℝ) / (48 * ((K + 1) * Real.logb 2 (2 / α) / α)) ≤
      α ^ 2 * (n : ℝ) / (48 * ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hk1 (show (0 : ℝ) ≤ 48 by norm_num)
  have hgoal : (1 / (48 * (K + 1))) * (α ^ 3 / Real.logb 2 (2 / α)) * (n : ℝ) ≤
      (X₃.ncard : ℝ) :=
    le_trans (le_trans heq2.le hcmp2) hX3
  linarith [hgoal, hle1R]


namespace CycleLengthsExp.ManyLengths

/-- Ascribed alias matching the published node name (submission-time shape). -/
theorem theorem_2 : ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      CycleLengthsExp.WellSpread.IsAlphaExpander α G →
        c * (α ^ 3 / Real.logb 2 (2 / α)) * (n : ℝ) ≤
          ((CycleLengthsExp.WellSpread.cycleLengths G).ncard : ℝ) :=
  _root_.solution

end CycleLengthsExp.ManyLengths
