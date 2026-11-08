-- Prove2me | solution 1 for FriedmannParity.exponential_payoff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T03:56:16.961511+00:00
-- url     : https://prove2.me/submissions/2a658483-610f-48af-88d2-eb721ed489a2

import Definitions.Def_friedmann_parity_lib_binary_traj
import Definitions.Def_friedmann_payoff

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


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FriedmannParity

open scoped BigOperators

section SinkPayoffReduction

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Part 1: Optimal Counterstrategies and Two-Strategy Order Transport in 1-Sink Games -/

lemma exists_disc_sink_counterstrategy {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    ∃ ϱ : V → V,
      Legal G true ϱ ∧
      (∀ u, (playValue G σ ϱ u).cyclePriority = 1) ∧
      (∀ u, (playValue G σ ϱ u).path = (value G σ u).path) ∧
      (∀ u, FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ u =
        FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ ϱ u) ∧
      (∀ u τ, Legal G true τ →
        FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ ϱ u ≤
          FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ u) := by
  let H := FriedmannDiscounted.induced G
  have hG := isSinkGame_wellFormed hSink
  have hH := isSinkGame_wellFormed_induced hSink
  have hcp_val : ∀ u, (value G σ u).cyclePriority = 1 :=
    hSink.2.2.2.2.2.2 σ hσ hAbove
  rcases exists_optimalCounterstrategy G hG σ with ⟨τ_star, hτ_star⟩
  have hval_eq : ∀ u, value G σ u = playValue G σ τ_star u :=
    value_eq_playValue_of_optimalCounterstrategy hG hτ_star
  have hcp_star : ∀ u, (playValue G σ τ_star u).cyclePriority = 1 := by
    intro u
    rw [← hval_eq u]
    exact hcp_val u
  rcases exists_disc_optimalCounterstrategy hH σ with ⟨ϱ, hϱ_leg, hϱ_min, hϱ_val⟩
  have hcp_ϱ : ∀ u, (playValue G σ ϱ u).cyclePriority = 1 := by
    intro u
    have hle_u : ValueLE G (playValue G σ τ_star u) (playValue G σ ϱ u) :=
      hτ_star.2 u ϱ hϱ_leg
    have hrew_ge : reward 1 ≤ reward (playValue G σ ϱ u).cyclePriority := by
      have h := reward_cyclePriority_le_of_valueLE hle_u
      rwa [hcp_star u] at h
    by_contra hne_one
    have hcl_ne : cycleLeader G σ ϱ u ≠ sink := by
      intro hcl
      apply hne_one
      rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl, isSinkGame_priority_sink hSink]
    have hneg := discounted_playValue_lt_zero_of_cyclePriority_eq_one hSink (hcp_star u)
    have hpos := zero_lt_discounted_playValue_of_cycleLeader_ne_sink hSink hrew_ge hcl_ne
    have hmin_u := hϱ_min u τ_star hτ_star.1
    linarith
  have hpath_eq : ∀ u, (playValue G σ ϱ u).path = (value G σ u).path := by
    intro u
    rw [hval_eq u]
    have hle_u : ValueLE G (playValue G σ τ_star u) (playValue G σ ϱ u) :=
      hτ_star.2 u ϱ hϱ_leg
    rcases hle_u with heq | hlt
    · rw [heq]
    · exfalso
      rw [valueLT_iff_setLT_of_cyclePriority_eq_one hSink (hcp_star u) (hcp_ϱ u)] at hlt
      have hlt_disc := discounted_playValue_lt_of_setLT hSink (hcp_star u) (hcp_ϱ u) hlt
      have hmin_u := hϱ_min u τ_star hτ_star.1
      linarith
  exact ⟨ϱ, hϱ_leg, hcp_ϱ, hpath_eq, hϱ_val, hϱ_min⟩

lemma sink_discounted_order_le {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v))
    (v w : V) :
    ValueLE G (value G σ v) (value G σ w) ↔
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ v ≤
        FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ w := by
  have hG := isSinkGame_wellFormed hSink
  rw [valueLE_iff_not_valueLT hG.2, sink_discounted_order_lib G ι sink hSink σ hσ hAbove w v, not_lt]

lemma sink_discounted_order_two_lt {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ₁ σ₂ : V → V}
    (hσ₁ : Legal G false σ₁) (hAbove₁ : ∀ v, ValueLE G (value G ι v) (value G σ₁ v))
    (hσ₂ : Legal G false σ₂) (hAbove₂ : ∀ v, ValueLE G (value G ι v) (value G σ₂ v))
    (v₁ v₂ : V)
    (hlt : ValueLT G (value G σ₁ v₁) (value G σ₂ v₂)) :
    FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ₁ v₁ <
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ₂ v₂ := by
  have hG := isSinkGame_wellFormed hSink
  rcases exists_optimalCounterstrategy G hG σ₁ with ⟨τ₁, hτ₁⟩
  rcases exists_optimalCounterstrategy G hG σ₂ with ⟨τ₂, hτ₂⟩
  have hval₁ := value_eq_playValue_of_optimalCounterstrategy hG hτ₁ v₁
  have hval₂ := value_eq_playValue_of_optimalCounterstrategy hG hτ₂ v₂
  have hcp₁ : (playValue G σ₁ τ₁ v₁).cyclePriority = 1 := by
    rw [← hval₁]
    exact hSink.2.2.2.2.2.2 σ₁ hσ₁ hAbove₁ v₁
  have hcp₂ : (playValue G σ₂ τ₂ v₂).cyclePriority = 1 := by
    rw [← hval₂]
    exact hSink.2.2.2.2.2.2 σ₂ hσ₂ hAbove₂ v₂
  rw [hval₁, hval₂, valueLT_iff_setLT_of_cyclePriority_eq_one hSink hcp₁ hcp₂,
      ← hval₁, ← hval₂] at hlt
  rcases exists_disc_sink_counterstrategy hSink hσ₁ hAbove₁ with
    ⟨ϱ₁, _, hcp_ϱ₁, hpath₁, hval_disc₁, _⟩
  rcases exists_disc_sink_counterstrategy hSink hσ₂ hAbove₂ with
    ⟨ϱ₂, _, hcp_ϱ₂, hpath₂, hval_disc₂, _⟩
  rw [← hpath₁ v₁, ← hpath₂ v₂] at hlt
  rw [hval_disc₁ v₁, hval_disc₂ v₂]
  exact discounted_playValue_lt_of_setLT hSink (hcp_ϱ₁ v₁) (hcp_ϱ₂ v₂) hlt

lemma sink_discounted_order_two_le {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ₁ σ₂ : V → V}
    (hσ₁ : Legal G false σ₁) (hAbove₁ : ∀ v, ValueLE G (value G ι v) (value G σ₁ v))
    (hσ₂ : Legal G false σ₂) (hAbove₂ : ∀ v, ValueLE G (value G ι v) (value G σ₂ v))
    (v₁ v₂ : V)
    (hle : FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ₁ v₁ ≤
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ₂ v₂) :
    ValueLE G (value G σ₁ v₁) (value G σ₂ v₂) := by
  have hG := isSinkGame_wellFormed hSink
  rw [valueLE_iff_not_valueLT hG.2]
  intro hlt
  have hlt_disc := sink_discounted_order_two_lt hSink hσ₂ hAbove₂ hσ₁ hAbove₁ v₂ v₁ hlt
  linarith

/-! ### Part 2: Policy Iteration Predicates (`Improving`, `Improvable`, `Allowed`, `Improvement`, `LocalStep`) -/

lemma value_above_of_allowed {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ ρ : V → V}
    (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v))
    (hal : Allowed G σ ρ) (v : V) :
    ValueLE G (value G ι v) (value G ρ v) :=
  valueLE_trans (isSinkGame_wellFormed hSink).2 (hAbove v)
    (value_le_of_allowed (isSinkGame_wellFormed hSink) hal v)

lemma improving_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v))
    (v w : V) :
    Improving G σ v w ↔
      FriedmannScalar.Improving (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ v w := by
  unfold Improving FriedmannScalar.Improving
  rw [sink_discounted_order_lib G ι sink hSink σ hσ hAbove (σ v) w]
  rfl

lemma improvable_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    Improvable G σ ↔
      FriedmannScalar.Improvable (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ := by
  unfold Improvable FriedmannScalar.Improvable
  constructor
  · rintro ⟨v, w, h⟩
    exact ⟨v, w, (improving_induced_iff hSink hσ hAbove v w).mp h⟩
  · rintro ⟨v, w, h⟩
    exact ⟨v, w, (improving_induced_iff hSink hσ hAbove v w).mpr h⟩

lemma allowed_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ ρ : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    Allowed G σ ρ ↔
      FriedmannScalar.Allowed (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ ρ := by
  unfold Allowed FriedmannScalar.Allowed
  constructor
  · rintro ⟨hρ, hal⟩
    refine ⟨hρ, fun v hv => ?_⟩
    exact (sink_discounted_order_le hSink hσ hAbove (σ v) (ρ v)).mp (hal v hv)
  · rintro ⟨hρ, hal⟩
    refine ⟨hρ, fun v hv => ?_⟩
    exact (sink_discounted_order_le hSink hσ hAbove (σ v) (ρ v)).mpr (hal v hv)

lemma improvement_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ σ' : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    Improvement G σ σ' ↔
      FriedmannScalar.Improvement
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ σ' := by
  unfold Improvement FriedmannScalar.Improvement
  rw [allowed_induced_iff hSink hσ hAbove, improvable_induced_iff hSink hσ hAbove]
  constructor
  · rintro ⟨hal, himp⟩
    refine ⟨hal, fun h => ?_⟩
    rcases himp h with ⟨v, hv, hlt⟩
    exact ⟨v, hv, (sink_discounted_order_lib G ι sink hSink σ hσ hAbove (σ v) (σ' v)).mp hlt⟩
  · rintro ⟨hal, himp⟩
    refine ⟨hal, fun h => ?_⟩
    rcases himp h with ⟨v, hv, hlt⟩
    exact ⟨v, hv, (sink_discounted_order_lib G ι sink hSink σ hσ hAbove (σ v) (σ' v)).mpr hlt⟩

lemma localStep_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ σ' : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    LocalStep G σ σ' ↔
      FriedmannScalar.LocalStep
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ σ' := by
  unfold LocalStep FriedmannScalar.LocalStep
  rw [improvement_induced_iff hSink hσ hAbove]
  constructor
  · rintro ⟨himp, hloc⟩
    refine ⟨himp, fun v w hv hvw => ?_⟩
    exact (sink_discounted_order_le hSink hσ hAbove w (σ' v)).mp (hloc v w hv hvw)
  · rintro ⟨himp, hloc⟩
    refine ⟨himp, fun v w hv hvw => ?_⟩
    exact (sink_discounted_order_le hSink hσ hAbove w (σ' v)).mpr (hloc v w hv hvw)

/-! ### Part 3: Equivalence of `GlobalStep` -/

lemma discounted_value_le_of_step_le {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (ρ σ' : V → V)
    (hstep : ∀ u, H.arena.owner u = false →
      FriedmannScalar.value (FriedmannDiscounted.model H) σ' (ρ u) ≤
        FriedmannScalar.value (FriedmannDiscounted.model H) σ' (σ' u))
    (v : V) :
    FriedmannScalar.value (FriedmannDiscounted.model H) ρ v ≤
      FriedmannScalar.value (FriedmannDiscounted.model H) σ' v := by
  rcases exists_disc_optimalCounterstrategy hH σ' with ⟨ϱ, hϱ_leg, _, hϱ_val⟩
  rcases exists_disc_optimalCounterstrategy hH ρ with ⟨ϱ_ρ, _, hϱ_ρ_min, hϱ_ρ_val⟩
  have hle_ρ : FriedmannScalar.value (FriedmannDiscounted.model H) ρ v ≤
      FriedmannDiscounted.playValue H ρ ϱ v := by
    rw [hϱ_ρ_val v]
    exact hϱ_ρ_min v ϱ hϱ_leg
  suffices h : FriedmannDiscounted.playValue H ρ ϱ v ≤
      FriedmannDiscounted.playValue H σ' ϱ v by
    rw [hϱ_val v]
    exact le_trans hle_ρ h
  let f : V → ℚ := fun u =>
    FriedmannDiscounted.playValue H ρ ϱ u - FriedmannDiscounted.playValue H σ' ϱ u
  have hβ0 : 0 < H.discount := hH.2.1
  have hβ1 : H.discount < 1 := hH.2.2
  have hf_step : ∀ u, f u ≤ H.discount * f (step H.arena ρ ϱ u) := by
    intro u
    have h1 := discounted_playValue_step hH ρ ϱ u
    have h2 := discounted_playValue_step hH σ' ϱ u
    have hstep_u : FriedmannDiscounted.playValue H σ' ϱ (step H.arena ρ ϱ u) ≤
        FriedmannDiscounted.playValue H σ' ϱ (step H.arena σ' ϱ u) := by
      unfold step
      split_ifs with hu
      · rw [← hϱ_val (ρ u), ← hϱ_val (σ' u)]
        exact hstep u hu
      · exact le_rfl
    dsimp only [f]
    nlinarith
  have hne : (Finset.univ : Finset V).Nonempty := ⟨v, Finset.mem_univ v⟩
  set M_sup := Finset.univ.sup' hne f
  have hle_M : ∀ u, f u ≤ M_sup :=
    fun u => Finset.le_sup' f (Finset.mem_univ u)
  obtain ⟨u₀, _, hu₀⟩ := Finset.exists_mem_eq_sup' hne f
  have hM_step : M_sup ≤ H.discount * M_sup := by
    calc M_sup = f u₀ := hu₀
      _ ≤ H.discount * f (step H.arena ρ ϱ u₀) := hf_step u₀
      _ ≤ H.discount * M_sup := mul_le_mul_of_nonneg_left (hle_M _) (le_of_lt hβ0)
  have hM_nonpos : M_sup ≤ 0 := by nlinarith
  have hv := hle_M v
  dsimp only [f] at hv
  linarith

lemma owner_false_sink_apply_eq_sink {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {π : V → V}
    (hπ : Legal G false π) (hAbove : ∀ v, ValueLE G (value G ι v) (value G π v))
    (hsink_owner : G.owner sink = false) :
    π sink = sink := by
  have hG := isSinkGame_wellFormed hSink
  rcases exists_optimalCounterstrategy G hG π with ⟨τ, hτ⟩
  have hcp : (playValue G π τ sink).cyclePriority = 1 := by
    rw [← value_eq_playValue_of_optimalCounterstrategy hG hτ sink]
    exact hSink.2.2.2.2.2.2 π hπ hAbove sink
  have hstep := step_sink_eq_sink_of_cyclePriority_eq_one hSink hcp
  unfold step at hstep
  rw [if_pos hsink_owner] at hstep
  exact hstep

lemma value_step_le_of_globalStep_parity {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ σ' : V → V}
    (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v))
    (hglob : GlobalStep G σ σ')
    {v w : V} (hv : G.owner v = false) (hvw : G.edge v w)
    (hal_vw : ValueLE G (value G σ (σ v)) (value G σ w)) :
    ValueLE G (value G σ' w) (value G σ' (σ' v)) := by
  have hG := isSinkGame_wellFormed hSink
  rw [valueLE_iff_not_valueLT hG.2]
  intro hlt
  let ρ : V → V := Function.update σ' v w
  have hρ_leg : Legal G false ρ := by
    intro u hu
    dsimp only [ρ]
    by_cases huv : u = v
    · subst huv
      rw [Function.update_self]
      exact hvw
    · rw [Function.update_of_ne huv]
      exact hglob.1.1.1 u hu
  have hρ_al_σ : Allowed G σ ρ := by
    refine ⟨hρ_leg, fun u hu => ?_⟩
    dsimp only [ρ]
    by_cases huv : u = v
    · subst huv
      rw [Function.update_self]
      exact hal_vw
    · rw [Function.update_of_ne huv]
      exact hglob.1.1.2 u hu
  have hρ_al_σ' : Allowed G σ' ρ := by
    refine ⟨hρ_leg, fun u hu => ?_⟩
    dsimp only [ρ]
    by_cases huv : u = v
    · subst huv
      rw [Function.update_self]
      exact Or.inr hlt
    · rw [Function.update_of_ne huv]
      exact valueLE_refl G _
  have hAbove_σ' : ∀ u, ValueLE G (value G ι u) (value G σ' u) :=
    value_above_of_allowed hSink hAbove hglob.1.1
  have hAbove_ρ : ∀ u, ValueLE G (value G ι u) (value G ρ u) :=
    value_above_of_allowed hSink hAbove hρ_al_σ
  have hle_σ'_ρ : ∀ u, ValueLE G (value G σ' u) (value G ρ u) :=
    value_le_of_allowed hG hρ_al_σ'
  have hcp_σ' : ∀ u, (value G σ' u).cyclePriority = 1 :=
    hSink.2.2.2.2.2.2 σ' hglob.1.1.1 hAbove_σ'
  have hpv : G.priority v ≠ (value G σ' (σ' v)).cyclePriority := by
    rw [hcp_σ' (σ' v), ne_eq, isSinkGame_priority_eq_one_iff hSink v]
    rintro rfl
    have h1 := owner_false_sink_apply_eq_sink hSink hglob.1.1.1 hAbove_σ' hv
    have h2 := owner_false_sink_apply_eq_sink hSink hρ_leg hAbove_ρ hv
    dsimp only [ρ] at h2
    rw [Function.update_self] at h2
    rw [h1, h2] at hlt
    exact valueLT_irrefl hG.2 _ hlt
  have hlt_ρ : ValueLT G (value G σ' (σ' v)) (value G σ' (ρ v)) := by
    dsimp only [ρ]
    rw [Function.update_self]
    exact hlt
  have hlt_v : ValueLT G (value G σ' v) (value G ρ v) :=
    value_lt_of_improving_of_priority_ne_cyclePriority hG hle_σ'_ρ hv hlt_ρ hpv
  have hle_v : ValueLE G (value G ρ v) (value G σ' v) :=
    hglob.2 ρ hρ_al_σ v
  exact (valueLE_iff_not_valueLT hG.2 _ _).mp hle_v hlt_v

lemma globalStep_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ σ' : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    GlobalStep G σ σ' ↔
      FriedmannScalar.GlobalStep
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ σ' := by
  let H := FriedmannDiscounted.induced G
  let M := FriedmannDiscounted.model H
  have hH := isSinkGame_wellFormed_induced hSink
  constructor
  · intro hglob
    have himp_M : FriedmannScalar.Improvement M σ σ' :=
      (improvement_induced_iff hSink hσ hAbove).mp hglob.1
    have hAbove_σ' : ∀ u, ValueLE G (value G ι u) (value G σ' u) :=
      value_above_of_allowed hSink hAbove hglob.1.1
    refine ⟨himp_M, fun ρ hρ_M v => ?_⟩
    have hρ : Allowed G σ ρ := (allowed_induced_iff hSink hσ hAbove).mpr hρ_M
    apply discounted_value_le_of_step_le hH ρ σ' _ v
    intro u hu
    have hle_G : ValueLE G (value G σ' (ρ u)) (value G σ' (σ' u)) :=
      value_step_le_of_globalStep_parity hSink hAbove hglob hu (hρ.1 u hu) (hρ.2 u hu)
    exact (sink_discounted_order_le hSink hglob.1.1.1 hAbove_σ' (ρ u) (σ' u)).mp hle_G
  · rintro ⟨himp_M, hglob_M⟩
    have himp_G : Improvement G σ σ' :=
      (improvement_induced_iff hSink hσ hAbove).mpr himp_M
    have hAbove_σ' : ∀ u, ValueLE G (value G ι u) (value G σ' u) :=
      value_above_of_allowed hSink hAbove himp_G.1
    refine ⟨himp_G, fun ρ hρ_G v => ?_⟩
    have hAbove_ρ : ∀ u, ValueLE G (value G ι u) (value G ρ u) :=
      value_above_of_allowed hSink hAbove hρ_G
    have hρ_M : FriedmannScalar.Allowed M σ ρ :=
      (allowed_induced_iff hSink hσ hAbove).mp hρ_G
    exact sink_discounted_order_two_le hSink hρ_G.1 hAbove_ρ himp_G.1.1 hAbove_σ' v v
      (hglob_M ρ hρ_M v)

lemma rule_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (global : Bool) {σ σ' : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    (if global then GlobalStep G else LocalStep G) σ σ' ↔
      FriedmannScalar.rule
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) global σ σ' := by
  unfold FriedmannScalar.rule
  cases global
  · exact localStep_induced_iff hSink hσ hAbove
  · exact globalStep_induced_iff hSink hσ hAbove

/-! ### Part 4: Equivalence of `CompleteRun`, `HardInstance`, and Exponential Reduction -/

lemma allowed_of_rule_parity {G : Game V} (global : Bool) {σ σ' : V → V}
    (h : (if global then GlobalStep G else LocalStep G) σ σ') :
    Allowed G σ σ' := by
  cases global
  · exact h.1.1
  · exact h.1.1

lemma allowed_of_rule_scalar {M : FriedmannScalar.Model V} (global : Bool) {σ σ' : V → V}
    (h : FriedmannScalar.rule M global σ σ') :
    FriedmannScalar.Allowed M σ σ' := by
  unfold FriedmannScalar.rule at h
  cases global
  · exact h.1.1
  · exact h.1.1

lemma value_above_of_completeRun_parity {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (global : Bool) {T : ℕ} {run : ℕ → (V → V)}
    (hrun : CompleteRun G (if global then GlobalStep G else LocalStep G) ι T run) :
    ∀ t ≤ T, ∀ v, ValueLE G (value G ι v) (value G (run t) v) := by
  intro t
  induction t with
  | zero =>
    intro _ v
    rw [hrun.1]
    exact valueLE_refl G _
  | succ t ih =>
    intro ht v
    have hAbove_t := ih (le_of_lt ht)
    have hstep := (hrun.2.2.1 t ht).2
    have hal := allowed_of_rule_parity global hstep
    exact value_above_of_allowed hSink hAbove_t hal v

lemma value_above_of_completeRun_induced {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (global : Bool) {T : ℕ} {run : ℕ → (V → V)}
    (hrun : FriedmannScalar.CompleteRun
      (FriedmannDiscounted.model (FriedmannDiscounted.induced G))
      (FriedmannScalar.rule (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) global)
      ι T run) :
    ∀ t ≤ T, ∀ v, ValueLE G (value G ι v) (value G (run t) v) := by
  intro t
  induction t with
  | zero =>
    intro _ v
    rw [hrun.1]
    exact valueLE_refl G _
  | succ t ih =>
    intro ht v
    have hAbove_t := ih (le_of_lt ht)
    have hleg_t : Legal G false (run t) := hrun.2.1 t (le_of_lt ht)
    have hstep := (hrun.2.2.1 t ht).2
    have hal_M := allowed_of_rule_scalar global hstep
    have hal_G : Allowed G (run t) (run (t + 1)) :=
      (allowed_induced_iff hSink hleg_t hAbove_t).mpr hal_M
    exact value_above_of_allowed hSink hAbove_t hal_G v

lemma completeRun_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (global : Bool) (T : ℕ) (run : ℕ → (V → V)) :
    CompleteRun G (if global then GlobalStep G else LocalStep G) ι T run ↔
      FriedmannScalar.CompleteRun
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G))
        (FriedmannScalar.rule (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) global)
        ι T run := by
  constructor
  · intro hrun
    have hAbove := value_above_of_completeRun_parity hSink global hrun
    rcases hrun with ⟨h0, hleg, hstep, hterm⟩
    refine ⟨h0, hleg, ?_, ?_⟩
    · intro t ht
      have hleg_t := hleg t (le_of_lt ht)
      have hAbove_t := hAbove t (le_of_lt ht)
      rw [← improvable_induced_iff hSink hleg_t hAbove_t,
          ← rule_induced_iff hSink global hleg_t hAbove_t]
      exact hstep t ht
    · have hleg_T := hleg T le_rfl
      have hAbove_T := hAbove T le_rfl
      rw [← improvable_induced_iff hSink hleg_T hAbove_T]
      exact hterm
  · intro hrun
    have hAbove := value_above_of_completeRun_induced hSink global hrun
    rcases hrun with ⟨h0, hleg, hstep, hterm⟩
    refine ⟨h0, hleg, ?_, ?_⟩
    · intro t ht
      have hleg_t : Legal G false (run t) := hleg t (le_of_lt ht)
      have hAbove_t := hAbove t (le_of_lt ht)
      rw [improvable_induced_iff hSink hleg_t hAbove_t,
          rule_induced_iff hSink global hleg_t hAbove_t]
      exact hstep t ht
    · have hleg_T : Legal G false (run T) := hleg T le_rfl
      have hAbove_T := hAbove T le_rfl
      rw [improvable_induced_iff hSink hleg_T hAbove_T]
      exact hterm

theorem hardInstance_induced_of_isSinkGame {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (global : Bool) (iterations : ℕ)
    (hHard : HardInstance G ι (if global then GlobalStep G else LocalStep G) iterations) :
    FriedmannDiscounted.WellFormed (FriedmannDiscounted.induced G) ∧
      FriedmannScalar.HardInstance
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) ι
        (FriedmannScalar.rule (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) global)
        iterations := by
  refine ⟨isSinkGame_wellFormed_induced hSink, ?_⟩
  rcases hHard with ⟨_, hι, ⟨T₀, run₀, hrun₀⟩, hbound⟩
  refine ⟨hι, ⟨T₀, run₀, (completeRun_induced_iff hSink global T₀ run₀).mp hrun₀⟩, ?_⟩
  intro T run hrun
  exact hbound T run ((completeRun_induced_iff hSink global T run).mpr hrun)

theorem exponential_payoff_of_sink_family
    (hFamily : ∃ C : ℕ, 0 < C ∧ ∀ global : Bool, ∀ n : ℕ, 0 < n →
      ∃ N : ℕ, ∃ G : Game (Fin N), ∃ ι : Fin N → Fin N, ∃ sink : Fin N,
        edgeCount G ≤ C * n ∧
        IsSinkGame G ι sink ∧
        HardInstance G ι (if global then GlobalStep G else LocalStep G) (2 ^ n)) :
    FriedmannDiscounted.Exponential ∧
      FriedmannDiscounted.ExponentialMeanViaReduction := by
  rcases hFamily with ⟨C, hC, hExp⟩
  constructor
  · refine ⟨C, hC, ?_⟩
    intro global n hn
    rcases hExp global n hn with ⟨N, G, ι, sink, hedge, hSink, hHard⟩
    have hind := hardInstance_induced_of_isSinkGame hSink global (2 ^ n) hHard
    exact ⟨N, FriedmannDiscounted.induced G, ι, hind.1, hedge, hind.2⟩
  · refine ⟨C, hC, ?_⟩
    intro global n hn
    rcases hExp global n hn with ⟨N, G, ι, sink, hedge, hSink, hHard⟩
    have hind := hardInstance_induced_of_isSinkGame hSink global (2 ^ n) hHard
    exact ⟨N, G, ι, hSink.1, hedge, hind.1, hind.2⟩

theorem exponential_payoff_lib : FriedmannDiscounted.Exponential ∧
    FriedmannDiscounted.ExponentialMeanViaReduction := by
  apply exponential_payoff_of_sink_family
  rcases exponential_sink_family with ⟨C, hC, hExp⟩
  refine ⟨C, hC, fun global n hn => ?_⟩
  rcases hExp global n hn with ⟨N, G, ι, sink, _hbin, hedge, _hprio, hSink, hHard⟩
  exact ⟨N, G, ι, sink, hedge, hSink, hHard⟩

end SinkPayoffReduction

end FriedmannParity

open FriedmannParity in
theorem solution : FriedmannDiscounted.Exponential ∧
    FriedmannDiscounted.ExponentialMeanViaReduction :=
  FriedmannParity.exponential_payoff_lib
