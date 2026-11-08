-- Prove2me | solution 1 for FriedmannParity.exponential_binary
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T03:56:15.962497+00:00
-- url     : https://prove2.me/submissions/e2483f1c-e7d1-4520-a1d7-e1bc2dc6db3a

import Definitions.Def_friedmann_parity_lib_binary_traj
import Definitions.Def_friedmann_parity

set_option autoImplicit false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace FriedmannParity

lemma mem_portalCR_of_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
    {w_p : V_bin n} (hp : PortalCR glob n b s w_p)
    (u : V_bin n) (hu : (G_bin n).priority .s < (G_bin n).priority u) :
    u ∈ predPath glob n b s w_p ↔ highMemF n b ⟨lowestZero0 b n, lowestZero0_lt hclose.1⟩ u := by
  unfold PortalCR at hp
  rw [if_pos hclose] at hp
  have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
    dsimp [G_bin, priority_bin] at hu ⊢; omega
  have hne_r : u ≠ .r := by intro h; subst h; dsimp [G_bin, priority_bin] at hu; omega
  have hract : rActive0 n b s = true := by
    unfold rActive0; rw [decide_eq_true_eq]; exact Or.inr ⟨hclose.1, by omega⟩
  have hrtarg : (⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hract⟩ : Fin n) =
      ⟨lowestZero0 b n, lowestZero0_lt hclose.1⟩ := by
    apply Fin.ext; dsimp only; unfold rTarg0; rw [if_pos ⟨hclose.1, by omega⟩]
  rw [hp.2 u hp_u, highMem_r_of_true glob n b s hvalid hract u hp_u, hrtarg]
  simp [hne_r]

lemma mem_portalCR_zfk_of_not_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    {w_p : V_bin n} (hp : PortalCR glob n b s w_p)
    (j : Fin n) (u : V_bin n) (hu : u = .z j ∨ u = .f j ∨ u = .k j) :
    u ∈ predPath glob n b s w_p ↔ b.testBit j.val = true := by
  unfold PortalCR at hp
  rw [if_neg hnot_close] at hp
  have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
    rcases hu with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin]; omega }
  have hne_c : u ≠ .c := by rcases hu with rfl | rfl | rfl <;> nofun
  have hne_s : u ≠ .s := by rcases hu with rfl | rfl | rfl <;> nofun
  rw [hp.2 u hp_u]
  cases hsact : sActive0 n b s with
  | false =>
    have hb0 : b = 0 := by
      unfold sActive0 at hsact; rw [decide_eq_false_iff_not] at hsact; omega
    subst hb0
    rw [highMem_c_of_false glob n 0 s hvalid hsact, Nat.zero_testBit]
    simp [hne_c, hne_s]
  | true =>
    rw [highMem_c_of_true glob n b s hvalid hsact u hp_u]
    simp only [hne_c, hne_s, false_or]
    have hnot_s3 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b + 3 ≤ s) := by
      rintro ⟨hb_lt, hs3⟩
      have hmax := maxStep0_of_lt hb_lt
      have := hvalid.2.2
      exact hnot_close ⟨hb_lt, Or.inr (by omega)⟩
    have hb0 : 0 < b := by
      unfold sActive0 at hsact; rw [decide_eq_true_eq] at hsact
      exact hsact.resolve_right hnot_s3
    have hstarg : (⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hsact⟩ : Fin n) =
        ⟨lowestOne0 b n, lowestOne0_lt hb0 hvalid.2.1⟩ := by
      apply Fin.ext; dsimp only; unfold sTarg0; rw [if_neg hnot_s3]
    rw [hstarg]
    rcases hu with rfl | rfl | rfl <;> exact highMemF_lowestOne0_iff n b hb0 hvalid.2.1 j

lemma mem_hitsK_of_still_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false)
    {w_k : V_bin n} (hk : HitsK glob n b s w_k i)
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s w_k ↔ u = .k i ∨ highMemZ n b i u := by
  rw [hk u hu]
  have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid (.k i) (by nofun), hs_k, Finset.mem_insert]
  change u = .k i ∨ u ∈ predPath glob n b s (.z i) ↔ _
  rw [highMem_z glob n b s hvalid i hstill u hu]

theorem gkOrderProp_holds (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    GKOrderProp glob n b s i := by
  intro htau w_p w_k hp hk
  by_cases hC1 : b.testBit i.val = true ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s
  · have hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false := by
      intro hi1
      rcases hC1 with hbit | hT2
      · exact uStillH0_succ_false_of_testBit_true n b s i hi1 hbit
      · have hle_u : uLim0 b n ≤ n := le_trans (uLim0_le_hyLim0 b n s) (hyLim0_le_n b n s)
        unfold uStillH0
        rw [decide_eq_false_iff_not]
        dsimp only
        omega
    by_cases hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)
    · by_cases hil : i.val < lowestZero0 b n
      · have hcond : ¬((b.testBit i.val = true ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s) ∧
            ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) := by
          rintro ⟨_, hnot⟩; exact hnot ⟨hclose.1, hil, hclose.2⟩
        rw [if_neg hcond]
        let kFin : Fin n := ⟨lowestZero0 b n, lowestZero0_lt hclose.1⟩
        have hp_c : (G_bin n).priority .c ≤ (G_bin n).priority (.k kFin) := by
          dsimp [G_bin, priority_bin]; omega
        have hp_s : (G_bin n).priority .s < (G_bin n).priority (.k kFin) := by
          dsimp [G_bin, priority_bin]; omega
        apply predVal_lt_of_setLT glob n b s hvalid
        apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := .k kFin)
        · rw [mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.k kFin) hp_c]
          dsimp [highMemZ, kFin]
          rw [testBit_lowestZero0 hclose.1]
          rintro (h | ⟨_, htrue⟩)
          · injection h with h'; have := Fin.ext_iff.mp h'; dsimp [kFin] at this; omega
          · contradiction
        · rw [mem_portalCR_of_close glob n b s hvalid hclose hp (.k kFin) hp_s]
          exact Or.inl rfl
        · exact prio_k_even n kFin
        · intro u hu
          have hp_u_s : (G_bin n).priority .s < (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          have hp_u_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          rw [mem_hitsK_of_still_false glob n b s hvalid i hstill hk u hp_u_c,
              mem_portalCR_of_close glob n b s hvalid hclose hp u hp_u_s]
          rcases (prio_gt_s_iff n u).mp hp_u_s with ⟨j, rfl | rfl | rfl⟩
          · have hkj : lowestZero0 b n < j.val := by
              dsimp [G_bin, priority_bin, kFin] at hu; omega
            dsimp [highMemZ, highMemF]
            simp only [reduceCtorEq, false_or, Fin.ext_iff]
            exact ⟨fun h => h.elim (by omega) (fun ⟨_, hbj⟩ => Or.inr ⟨hkj, hbj⟩),
                   fun h => h.elim (by omega) (fun ⟨_, hbj⟩ => Or.inr ⟨by omega, hbj⟩)⟩
          · have hkj : lowestZero0 b n < j.val := by
              dsimp [G_bin, priority_bin, kFin] at hu; omega
            dsimp [highMemZ, highMemF]
            simp only [reduceCtorEq, false_or, Fin.ext_iff]
            exact ⟨fun ⟨_, hbj⟩ => Or.inr ⟨hkj, hbj⟩,
                   fun h => h.elim (by omega) (fun ⟨_, hbj⟩ => ⟨by omega, hbj⟩)⟩
          · have hkj : lowestZero0 b n < j.val := by
              dsimp [G_bin, priority_bin, kFin] at hu; omega
            dsimp [highMemZ, highMemF]
            constructor
            · rintro (h | ⟨_, hbj⟩)
              · injection h with h'; have := Fin.ext_iff.mp h'; omega
              · exact Or.inr ⟨hkj, hbj⟩
            · rintro (heq | ⟨_, hbj⟩)
              · have := Fin.ext_iff.mp heq; dsimp only at this; omega
              · exact Or.inr ⟨by omega, hbj⟩
      · have hcond : (b.testBit i.val = true ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s) ∧
            ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) :=
          ⟨hC1, fun ⟨_, hil', _⟩ => hil hil'⟩
        rw [if_pos hcond]
        have hi_eq_or_gt : i.val = lowestZero0 b n ∨ (lowestZero0 b n < i.val ∧ b.testBit i.val = true) := by
          rcases hC1 with hbit | hT2
          · by_cases heq : i.val = lowestZero0 b n
            · exact Or.inl heq
            · exact Or.inr ⟨by omega, hbit⟩
          · cases hbi : b.testBit i.val with
            | true =>
              by_cases heq : i.val = lowestZero0 b n
              · exact Or.inl heq
              · exact Or.inr ⟨by omega, rfl⟩
            | false =>
              have hle_lz : lowestZero0 b n ≤ i.val := lowestZero0_le_of_testBit_false i.isLt hbi
              have hclose2 := hclose.2
              unfold S_close0 at hclose2
              exact Or.inl (by omega)
        apply predVal_lt_of_setLT glob n b s hvalid
        apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := .f i)
        · rw [mem_portalCR_of_close glob n b s hvalid hclose hp (.f i) (by dsimp [G_bin, priority_bin]; omega)]
          dsimp [highMemF]
          rcases hi_eq_or_gt with heq | ⟨hlt, hbit⟩
          · left; exact Fin.ext heq
          · right; exact ⟨hlt, hbit⟩
        · rw [mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.f i) (by dsimp [G_bin, priority_bin]; omega)]
          dsimp [highMemZ]
          rintro (h | ⟨hlt, _⟩)
          · cases h
          · omega
        · exact prio_f_odd n i
        · intro u hu
          have hp_u_s : (G_bin n).priority .s < (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          have hp_u_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          rcases (prio_gt_s_iff n u).mp hp_u_s with ⟨j, rfl | rfl | rfl⟩
          · have hij : i.val < j.val := by dsimp [G_bin, priority_bin] at hu; omega
            rw [mem_portalCR_of_close glob n b s hvalid hclose hp (.z j) hp_u_s,
                mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.z j) hp_u_c]
            dsimp [highMemF, highMemZ]
            simp only [reduceCtorEq, false_or, Fin.ext_iff]
            exact ⟨fun h => h.elim (by omega) (fun ⟨_, hbj⟩ => Or.inr ⟨hij, hbj⟩),
                   fun h => h.elim (by omega) (fun ⟨_, hbj⟩ => Or.inr ⟨by omega, hbj⟩)⟩
          · have hij : i.val < j.val := by dsimp [G_bin, priority_bin] at hu; omega
            rw [mem_portalCR_of_close glob n b s hvalid hclose hp (.f j) hp_u_s,
                mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.f j) hp_u_c]
            dsimp [highMemF, highMemZ]
            simp only [reduceCtorEq, false_or, Fin.ext_iff]
            exact ⟨fun h => h.elim (by omega) (fun ⟨_, hbj⟩ => ⟨hij, hbj⟩),
                   fun ⟨_, hbj⟩ => Or.inr ⟨by omega, hbj⟩⟩
          · have hij_le : i.val ≤ j.val := by dsimp [G_bin, priority_bin] at hu; omega
            rw [mem_portalCR_of_close glob n b s hvalid hclose hp (.k j) hp_u_s,
                mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.k j) hp_u_c]
            dsimp [highMemF, highMemZ]
            by_cases heq : j.val = i.val
            · have hj_eq : j = i := Fin.ext heq
              subst hj_eq
              simp only [true_or, iff_true]
              rcases hi_eq_or_gt with heq_lz | ⟨hlt_lz, hbit⟩
              · exact Or.inl (Fin.ext heq_lz)
              · exact Or.inr ⟨hlt_lz, hbit⟩
            · have hij : i.val < j.val := by omega
              constructor
              · rintro (heq_lz | ⟨_, hbj⟩)
                · have := Fin.ext_iff.mp heq_lz; dsimp only at this; omega
                · exact Or.inr ⟨hij, hbj⟩
              · rintro (h | ⟨_, hbj⟩)
                · injection h with h'; have := Fin.ext_iff.mp h'; omega
                · exact Or.inr ⟨by omega, hbj⟩
    · have hcond : (b.testBit i.val = true ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s) ∧
          ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) :=
        ⟨hC1, fun ⟨hb_lt, _, h23⟩ => hclose ⟨hb_lt, h23⟩⟩
      rw [if_pos hcond]
      apply predVal_lt_of_setLT glob n b s hvalid
      cases hbit : b.testBit i.val with
      | true =>
        apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := .f i)
        · rw [mem_portalCR_zfk_of_not_close glob n b s hvalid hclose hp i (.f i) (Or.inr (Or.inl rfl))]
          exact hbit
        · rw [mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.f i) (by dsimp [G_bin, priority_bin]; omega)]
          dsimp [highMemZ]
          rintro (h | ⟨hlt, _⟩)
          · cases h
          · omega
        · exact prio_f_odd n i
        · intro u hu
          have hp_u_s : (G_bin n).priority .s < (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          have hp_u_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          rcases (prio_gt_s_iff n u).mp hp_u_s with ⟨j, rfl | rfl | rfl⟩
          · have hij : i.val < j.val := by dsimp [G_bin, priority_bin] at hu; omega
            rw [mem_portalCR_zfk_of_not_close glob n b s hvalid hclose hp j (.z j) (Or.inl rfl),
                mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.z j) hp_u_c]
            dsimp [highMemZ]
            simp only [reduceCtorEq, false_or, Fin.ext_iff]
            exact ⟨fun h => Or.inr ⟨hij, h⟩, fun h => h.elim (by omega) And.right⟩
          · have hij : i.val < j.val := by dsimp [G_bin, priority_bin] at hu; omega
            rw [mem_portalCR_zfk_of_not_close glob n b s hvalid hclose hp j (.f j) (Or.inr (Or.inl rfl)),
                mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.f j) hp_u_c]
            dsimp [highMemZ]
            simp only [reduceCtorEq, false_or]
            exact ⟨fun h => ⟨hij, h⟩, And.right⟩
          · have hij_le : i.val ≤ j.val := by dsimp [G_bin, priority_bin] at hu; omega
            rw [mem_portalCR_zfk_of_not_close glob n b s hvalid hclose hp j (.k j) (Or.inr (Or.inr rfl)),
                mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.k j) hp_u_c]
            dsimp [highMemZ]
            by_cases heq : j.val = i.val
            · have hj_eq : j = i := Fin.ext heq
              subst hj_eq
              simp [hbit]
            · have hij : i.val < j.val := by omega
              constructor
              · intro h; exact Or.inr ⟨hij, h⟩
              · rintro (h | ⟨_, h⟩)
                · injection h with h'; have := Fin.ext_iff.mp h'; omega
                · exact h
      | false =>
        apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := .k i)
        · rw [mem_portalCR_zfk_of_not_close glob n b s hvalid hclose hp i (.k i) (Or.inr (Or.inr rfl)), hbit]
          decide
        · rw [mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.k i) (by dsimp [G_bin, priority_bin]; omega)]
          exact Or.inl rfl
        · exact prio_k_even n i
        · intro u hu
          have hp_u_s : (G_bin n).priority .s < (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          have hp_u_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          rcases (prio_gt_s_iff n u).mp hp_u_s with ⟨j, rfl | rfl | rfl⟩
          · have hij : i.val < j.val := by dsimp [G_bin, priority_bin] at hu; omega
            rw [mem_portalCR_zfk_of_not_close glob n b s hvalid hclose hp j (.z j) (Or.inl rfl),
                mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.z j) hp_u_c]
            dsimp [highMemZ]
            simp only [reduceCtorEq, false_or, Fin.ext_iff]
            exact ⟨fun h => Or.inr ⟨hij, h⟩, fun h => h.elim (by omega) And.right⟩
          · have hij : i.val < j.val := by dsimp [G_bin, priority_bin] at hu; omega
            rw [mem_portalCR_zfk_of_not_close glob n b s hvalid hclose hp j (.f j) (Or.inr (Or.inl rfl)),
                mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.f j) hp_u_c]
            dsimp [highMemZ]
            simp only [reduceCtorEq, false_or]
            exact ⟨fun h => ⟨hij, h⟩, And.right⟩
          · have hij : i.val < j.val := by dsimp [G_bin, priority_bin] at hu; omega
            rw [mem_portalCR_zfk_of_not_close glob n b s hvalid hclose hp j (.k j) (Or.inr (Or.inr rfl)),
                mem_hitsK_of_still_false glob n b s hvalid i hstill hk (.k j) hp_u_c]
            dsimp [highMemZ]
            constructor
            · intro h; exact Or.inr ⟨hij, h⟩
            · rintro (h | ⟨_, h⟩)
              · injection h with h'; have := Fin.ext_iff.mp h'; omega
              · exact h
  · have hcond : ¬((b.testBit i.val = true ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s) ∧
        ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :=
      fun ⟨h1, _⟩ => hC1 h1
    rw [if_neg hcond]
    have hbit : b.testBit i.val = false := by
      cases h : b.testBit i.val with
      | false => rfl
      | true => exfalso; exact hC1 (Or.inl h)
    have hlt_T : ¬(3 * (n + 2 * i.val + 1) + 2 ≤ s) := fun h => hC1 (Or.inr h)
    have hstill : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + 1 + s < uLim0 b n := by
      dsimp [chooseTauEdge1] at htau
      simp [hbit, hlt_T] at htau
      exact htau
    rcases hstill with ⟨hb0, hikp, hlt_u⟩
    have hle_kp := uLim0_le_lowestOne0 b n
    have hkp_lt := lowestOne0_lt hb0 hvalid.2.1
    let m₀ : Fin n := ⟨uLim0 b n - 1 - s, by omega⟩
    have hi1 : i.val + 1 < n := by omega
    have hhi : hasHigherOne0 b n i.val = true := by
      rw [hasHigherOne0_iff]
      exact ⟨lowestOne0 b n, hikp, hkp_lt, testBit_lowestOne0 hb0 hvalid.2.1⟩
    have hce_z : chooseEdge1 glob n b s (.z i) = true := by
      dsimp [chooseEdge1]; simp [hi1, hhi]
    have hs_z : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z i) = .u ⟨i.val + 1, hi1⟩ := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_z]; dsimp [edge1]; rw [dif_pos hi1]
    have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
    have hu_hit := hitsWithTop_u_of_still glob n b s hvalid hb0 m₀ rfl (by dsimp [m₀]; omega)
      n ⟨i.val + 1, hi1⟩ (by dsimp [m₀]; omega) (by dsimp only; omega) (by dsimp [m₀]; omega)
    have hz_hit : HitsWithTop glob n b s (.z i) (.g m₀) (.f m₀) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.z i) (.g m₀) (.f m₀) (by nofun)
      · dsimp [G_bin, priority_bin, m₀]; omega
      · rw [hs_z]; exact hu_hit
    have hk_hit : HitsWithTop glob n b s (.k i) (.g m₀) (.f m₀) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.k i) (.g m₀) (.f m₀) (by nofun)
      · dsimp [G_bin, priority_bin, m₀]; omega
      · rw [hs_k]; exact hz_hit
    have hwk_hit : HitsWithTop glob n b s w_k (.g m₀) (.f m₀) := by
      refine ⟨hk_hit.1, ?_, ?_⟩
      · rw [hk (.f m₀) (by dsimp [G_bin, priority_bin]; omega)]
        exact hk_hit.2.1
      · intro u hu
        rw [hk u (by dsimp [G_bin, priority_bin] at hu ⊢; omega)]
        exact hk_hit.2.2 u hu
    have hport_or : HitsPortal glob n b s w_p .c ∨ HitsPortal glob n b s w_p .r := by
      unfold PortalCR at hp
      split_ifs at hp with hcl
      · exact Or.inr hp
      · exact Or.inl hp
    exact predVal_lt_portal_of_hitsWithTop_still glob n b s hvalid hb0 m₀ rfl (by dsimp [m₀]; omega)
      hwk_hit hport_or

theorem bestEdge_all (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (v : V_bin n) :
    BestEdgeProp glob n b s v := by
  have hport := portalOrderProp_holds glob n b s hvalid
  cases v with
  | r_2 => exact bestEdge_r_2 glob n b s hvalid hport
  | a k => exact bestEdge_a glob n b s hvalid hport k
  | l1 m => exact bestEdge_l1 glob n b s hvalid hport m
  | l2 m => exact bestEdge_l2 glob n b s hvalid hport m
  | l3 m => exact bestEdge_l3 glob n b s hvalid hport m
  | lp1 m => exact bestEdge_lp1 glob n b s hvalid hport m
  | lp2 m => exact bestEdge_lp2 glob n b s hvalid hport m
  | lp3 m => exact bestEdge_lp3 glob n b s hvalid hport m
  | r => exact bestEdge_r glob n b s hvalid
  | s => exact bestEdge_s glob n b s hvalid
  | rp i => exact bestEdge_rp glob n b s hvalid i
  | sp i => exact bestEdge_sp glob n b s hvalid i
  | z i => exact bestEdge_z glob n b s hvalid i
  | u i => exact bestEdge_u glob n b s hvalid i
  | hy i => exact bestEdge_hy glob n b s hvalid i
  | hx i => exact bestEdge_hx glob n b s hvalid i
  | h i => exact bestEdge_h glob n b s hvalid i
  | d3 i => exact bestEdge_d3 glob n b s hvalid hport i (gkOrderProp_holds glob n b s hvalid i)
  | d2 i => exact bestEdge_d2 glob n b s hvalid hport i (gkOrderProp_holds glob n b s hvalid i)
  | d1 i => exact bestEdge_d1 glob n b s hvalid hport i (gkOrderProp_holds glob n b s hvalid i)
  | x | r_2_odd | r_a | c_odd | c | f _ | g _ | k _ | b _ =>
    intro howner _
    dsimp [G_bin, owner_bin] at howner
    contradiction

theorem exponential_sink_family :
    ∃ C : ℕ, 0 < C ∧ ∀ global : Bool, ∀ n : ℕ, 0 < n →
      ∃ N : ℕ, ∃ G : Game (Fin N), ∃ ι : Fin N → Fin N, ∃ sink : Fin N,
        Binary G ∧ edgeCount G ≤ C * n ∧
        (∀ v, G.priority v ≤ C * n) ∧
        IsSinkGame G ι sink ∧
        HardInstance G ι (if global then GlobalStep G else LocalStep G) (2 ^ n) :=
  exponential_sink_family_of_bestEdge predTau0_optimal bestEdge_all

theorem exponential_binary_lib : ExponentialBinary :=
  exponential_binary_of_bestEdge predTau0_optimal bestEdge_all

end FriedmannParity

open FriedmannParity in
theorem solution : ExponentialBinary :=
  FriedmannParity.exponential_binary_lib
