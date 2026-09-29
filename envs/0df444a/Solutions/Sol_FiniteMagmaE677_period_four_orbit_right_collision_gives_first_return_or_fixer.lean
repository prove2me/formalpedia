-- Prove2me | solution 1 for FiniteMagmaE677.period_four_orbit_right_collision_gives_first_return_or_fixer
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-23T20:56:38.238043+00:00
-- url     : https://prove2.me/submissions/abbb1080-81be-49ba-9fa9-1077279643d7

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna.
-/
import Definitions.Def_FiniteMagmaE677_d4_first_return
import Definitions.Def_FiniteMagmaE677_seventh_element_growth
import Theorems.Thm_FiniteMagmaE677_period_four_orbit_right_collision_gives_seventh_element_or_fixer
import Mathlib.Tactic

/- Generic exact-period helper, inlined to remove a local Solutions dependency. -/
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna.
-/

namespace FiniteMagmaE677.FirstReturn

universe u

namespace D4Trace

theorem next_eq_seed_or_extend_of_leftInjective
    {α : Type u} {op : α → α → α} {x c1 c2 c3 seed : α} {n : ℕ}
    (leftInjective : Function.Injective (op x))
    (hxc1 : op x x = c1) (hc1c2 : op x c1 = c2)
    (hc2c3 : op x c2 = c3) (hc3x : op x c3 = x)
    (htrace : D4Trace op x c1 c2 c3 seed n) :
    orbitPoint op x (n + 1) seed = seed ∨
      D4Trace op x c1 c2 c3 seed (n + 1) := by
  let f : α → α := op x
  have hnext_step : f (orbitPoint op x n seed) = orbitPoint op x (n + 1) seed := by
    exact (Function.iterate_succ_apply' f n seed).symm
  by_cases hreturn : orbitPoint op x (n + 1) seed = seed
  · exact Or.inl hreturn
  · right
    have hnext_ne_x : orbitPoint op x (n + 1) seed ≠ x := by
      intro heq
      have hn_eq_c3 : orbitPoint op x n seed = c3 := by
        apply leftInjective
        calc
          f (orbitPoint op x n seed) = orbitPoint op x (n + 1) seed := hnext_step
          _ = x := heq
          _ = f c3 := by simpa [f] using hc3x.symm
      exact (htrace.outside n le_rfl).2.2.2 hn_eq_c3
    have hnext_ne_c1 : orbitPoint op x (n + 1) seed ≠ c1 := by
      intro heq
      have hn_eq_x : orbitPoint op x n seed = x := by
        apply leftInjective
        calc
          f (orbitPoint op x n seed) = orbitPoint op x (n + 1) seed := hnext_step
          _ = c1 := heq
          _ = f x := by simpa [f] using hxc1.symm
      exact (htrace.outside n le_rfl).1 hn_eq_x
    have hnext_ne_c2 : orbitPoint op x (n + 1) seed ≠ c2 := by
      intro heq
      have hn_eq_c1 : orbitPoint op x n seed = c1 := by
        apply leftInjective
        calc
          f (orbitPoint op x n seed) = orbitPoint op x (n + 1) seed := hnext_step
          _ = c2 := heq
          _ = f c1 := by simpa [f] using hc1c2.symm
      exact (htrace.outside n le_rfl).2.1 hn_eq_c1
    have hnext_ne_c3 : orbitPoint op x (n + 1) seed ≠ c3 := by
      intro heq
      have hn_eq_c2 : orbitPoint op x n seed = c2 := by
        apply leftInjective
        calc
          f (orbitPoint op x n seed) = orbitPoint op x (n + 1) seed := hnext_step
          _ = c3 := heq
          _ = f c2 := by simpa [f] using hc2c3.symm
      exact (htrace.outside n le_rfl).2.2.1 hn_eq_c2
    have hnext_ne_prior : ∀ i, i ≤ n →
        orbitPoint op x (n + 1) seed ≠ orbitPoint op x i seed := by
      intro i hi heq
      cases i with
      | zero => exact hreturn heq
      | succ k =>
          have hk : k ≤ n := by omega
          have hn_eq_hk : orbitPoint op x n seed = orbitPoint op x k seed := by
            apply leftInjective
            calc
              f (orbitPoint op x n seed) = orbitPoint op x (n + 1) seed := hnext_step
              _ = orbitPoint op x (Nat.succ k) seed := heq
              _ = f (orbitPoint op x k seed) := Function.iterate_succ_apply' f k seed
          have hnk := htrace.index_injective n le_rfl k hk hn_eq_hk
          omega
    refine { outside := ?_, index_injective := ?_ }
    · intro i hi
      by_cases hin : i ≤ n
      · exact htrace.outside i hin
      · have hi_eq : i = n + 1 := by omega
        subst i
        exact ⟨hnext_ne_x, hnext_ne_c1, hnext_ne_c2, hnext_ne_c3⟩
    · intro i hi j hj hij
      by_cases hin : i ≤ n
      · by_cases hjn : j ≤ n
        · exact htrace.index_injective i hin j hjn hij
        · have hj_eq : j = n + 1 := by omega
          subst j
          exact False.elim (hnext_ne_prior i hin hij.symm)
      · have hi_eq : i = n + 1 := by omega
        subst i
        by_cases hjn : j ≤ n
        · exact False.elim (hnext_ne_prior j hjn hij)
        · omega

end D4Trace

private noncomputable def finiteFirstReturn
    {α : Type u} [Finite α] (op : α → α → α)
    {x c1 c2 c3 seed : α} {n : ℕ}
    (leftInjective : Function.Injective (op x))
    (hxc1 : op x x = c1) (hc1c2 : op x c1 = c2)
    (hc2c3 : op x c2 = c3) (hc3x : op x c3 = x)
    (htrace : D4Trace op x c1 c2 c3 seed n) :
    D4FirstReturn op x c1 c2 c3 seed n := by
  let f : α → α := op x
  let d : ℕ := Function.minimalPeriod f seed
  have hseed_periodic : seed ∈ Function.periodicPts f :=
    leftInjective.mem_periodicPts seed
  have hd_pos : 0 < d := by
    simpa only [d] using Function.minimalPeriod_pos_of_mem_periodicPts hseed_periodic
  have hreturns : (f^[d]) seed = seed := by
    simpa only [d] using (Function.iterate_minimalPeriod (f := f) (x := seed))
  have hn_lt_d : n < d := by
    by_contra hn_not_lt
    have hd_le_n : d ≤ n := Nat.le_of_not_gt hn_not_lt
    have hd_eq_zero : d = 0 := htrace.index_injective d hd_le_n 0 (Nat.zero_le n) (by
      simpa only [orbitPoint, Function.iterate_zero_apply] using hreturns)
    exact (Nat.ne_of_gt hd_pos) hd_eq_zero
  have htrace_until : ∀ m, n ≤ m → m < d → D4Trace op x c1 c2 c3 seed m := by
    intro m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro _; exact htrace
    | succ k hnk ih =>
        intro hk_succ_lt_d
        have hk_lt_d : k < d := by omega
        have htrace_k := ih hk_lt_d
        have next := D4Trace.next_eq_seed_or_extend_of_leftInjective
          leftInjective hxc1 hc1c2 hc2c3 hc3x htrace_k
        rcases next with hreturn | hextend
        · have hk_succ_eq_zero : k + 1 = 0 := by
            apply Function.iterate_injOn_Iio_minimalPeriod
            · simpa only [d, f, Set.mem_Iio] using hk_succ_lt_d
            · simpa only [d, f, Set.mem_Iio] using hd_pos
            · simpa only [orbitPoint, Function.iterate_zero_apply] using hreturn
          omega
        · exact hextend
  have hn_le_before : n ≤ d - 1 := Nat.le_sub_one_of_lt hn_lt_d
  have hbefore_lt_d : d - 1 < d := Nat.sub_one_lt (Nat.ne_of_gt hd_pos)
  refine ⟨d, hd_pos, ?_, hn_lt_d, ?_, htrace_until (d - 1) hn_le_before hbefore_lt_d⟩
  · simp only [d, f]
  · simpa only [orbitPoint] using hreturns

noncomputable def firstReturn_of_initialization {α : Type u} [Fintype α]
    {op : α → α → α} {x c1 c2 c3 : α}
    (leftInjective : Function.Injective (op x))
    (init : D4Initialization op x c1 c2 c3) :
    D4FirstReturnPacket op x c1 c2 c3 := by
  let p := init.distinguished
  have fr {seed : α} {n : ℕ} (trace : D4Trace op x c1 c2 c3 seed n) :
      D4FirstReturn op x c1 c2 c3 seed n :=
    finiteFirstReturn op leftInjective p.orbit_c1 p.orbit_c2 p.orbit_c3 p.orbit_closes trace
  refine ⟨p, ?_⟩
  cases init.branch with
  | rSeedQThroughOne start fresh trace =>
      exact .rSeedQThroughOne start fresh trace (fr trace)
  | rSeedQThroughTwo start q_to_r fresh trace =>
      exact .rSeedQThroughTwo start q_to_r fresh trace (fr trace)
  | sSeedQThroughOne start fresh trace =>
      exact .sSeedQThroughOne start fresh trace (fr trace)
  | sSeedQThroughTwo start q_to_s fresh trace =>
      exact .sSeedQThroughTwo start q_to_s fresh trace (fr trace)
  | sSwapSeedT start q_to_s s_to_q fresh trace bridge =>
      exact .sSwapSeedT start q_to_s s_to_q fresh trace (fr trace) bridge

theorem leftInjective_of_E677 {α : Type u} [Fintype α]
    {op : α → α → α} (h : E677 op) (x : α) : Function.Injective (op x) := by
  have hs : Function.Surjective (op x) := by
    intro z
    exact ⟨op z (op (op x z) x), (h z x).symm⟩
  exact ((Finite.surjective_iff_bijective).mp hs).1

noncomputable def e677_firstReturnReduction {α : Type u} [Fintype α]
    {op : α → α → α} (h : E677 op)
    {x c1 c2 c3 : α} (init : D4Initialization op x c1 c2 c3) :
    D4FirstReturnPacket op x c1 c2 c3 :=
  firstReturn_of_initialization (leftInjective_of_E677 h x) init

end FiniteMagmaE677.FirstReturn

namespace FiniteMagmaE677.FirstReturn
universe u

theorem tagged_of_growth {α : Type u} [Fintype α] (op : α → α → α)
    (h : E677 op) {x c1 c2 c3 : α} (p : D4Distinguished op x c1 c2 c3)
    (growth : SeventhElementGrowth op x c1 c2 c3) :
    RTaggedStart op x c1 c2 c3 ∨ STaggedStart op x c1 c2 c3 := by
  have cancel := leftInjective_of_E677 h
  have outside (z : α) (hz : z ≠ x ∧ z ≠ c1 ∧ z ≠ c2 ∧ z ≠ c3) :
      op x z ≠ x ∧ op x z ≠ c1 ∧ op x z ≠ c2 ∧ op x z ≠ c3 := by
    exact ⟨fun e => hz.2.2.2 (cancel x (e.trans p.orbit_closes.symm)),
      fun e => hz.1 (cancel x (e.trans p.orbit_c1.symm)),
      fun e => hz.2.1 (cancel x (e.trans p.orbit_c2.symm)),
      fun e => hz.2.2.1 (cancel x (e.trans p.orbit_c3.symm))⟩
  have c1x : op c1 x = c2 := by
    apply cancel x
    apply cancel x
    simpa only [p.orbit_c1, p.orbit_c3, p.orbit_closes] using (h x x).symm
  have preq : op x (op c2 c1) = op c2 x := by
    apply cancel c1
    simpa only [c1x, p.q_packet_preimage] using (h x c1).symm
  have xq_ne : op x (op c2 x) ≠ op c2 x := by
    intro e
    exact p.x_ne_c1 (cancel c2 (cancel x (e.trans preq.symm)))
  have oq := outside (op c2 x) ⟨p.q_ne_x, p.q_ne_c1, p.q_ne_c2, p.q_ne_c3⟩
  rcases growth with ⟨_, _, _, _, _, _, _, hr | hs⟩
  · rcases hr with ⟨hr, fresh⟩
    left
    refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ?_⟩
    by_cases e : op x (op c2 x) = op c1 c2
    · right
      refine ⟨e, ?_⟩
      rcases fresh with f | f
      · exact False.elim (f.2.2.2.2.2 e)
      · exact f
    · exact Or.inl ⟨oq.1, oq.2.1, oq.2.2.1, oq.2.2.2, xq_ne, e⟩
  · rcases hs with ⟨hs, fresh⟩
    right
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2, ?_⟩
    by_cases e : op x (op c2 x) = op c3 (op c2 x)
    · by_cases e2 : op x (op c3 (op c2 x)) = op c2 x
      · apply Or.inr ∘ Or.inr
        refine ⟨e, e2, ?_, ?_⟩
        · rcases fresh with f | f | f
          · exact False.elim (f.2.2.2.2.2 e)
          · exact False.elim (f.2.2.2.2.1 e2)
          · exact f
        · have back (a b : α) : op (op a b) (op (op a (op a b)) a) = b := by
            apply cancel a
            exact (h (op a b) a).symm
          have transport : op (op c3 (op c2 x)) c3 = c1 := by
            apply cancel (op c2 x)
            calc
              op (op c2 x) (op (op c3 (op c2 x)) c3) = x := by
                simpa only [← p.q_collision] using back c3 x
              _ = op (op c2 x) c1 := by
                simpa only [p.q_packet_return, hs.1] using (back c2 x).symm
          have c2c1 : op c2 c1 = op c3 (op c2 x) := cancel x (preq.trans e2.symm)
          apply cancel (op c3 (op c2 x))
          calc
            op (op c3 (op c2 x)) (op (op c2 (op c3 (op c2 x))) c2) = c1 := by
              simpa only [c2c1] using back c2 c1
            _ = op (op c3 (op c2 x)) c3 := transport.symm
      · have os := outside (op c3 (op c2 x))
            ⟨hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
        exact Or.inr (Or.inl ⟨e, os.1, os.2.1, os.2.2.1, os.2.2.2, e2,
          fun es => hs.2.2.2.2.2 (cancel x (es.trans e.symm))⟩)
    · exact Or.inl ⟨oq.1, oq.2.1, oq.2.2.1, oq.2.2.2, xq_ne, e⟩

end FiniteMagmaE677.FirstReturn

/- Collision ingress, with its local Solutions imports removed. -/
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

/-!
# Collision ingress to the finite D4 first-return packet

The proved seven-element growth disjunction is normalized into the explicit
first-return API.  The finite first-return constructor then supplies the exact
periodic packet, while the alternative remains a fixer at `x`.
-/

universe u

namespace FiniteMagmaE677
open FirstReturn

private theorem c12_ne
    {α : Type u} [Fintype α] (op : α → α → α)
    (h : E677 op) {x c1 c2 c3 : α}
    (hc1 : op x x = c1) (hc2 : op x c1 = c2) (hc3 : op x c2 = c3)
    (hx1 : x ≠ c1) (hx2 : x ≠ c2) :
    c1 ≠ c2 ∧ c1 ≠ c3 ∧ c2 ≠ c3 := by
  have cancel : ∀ a b c : α, op a b = op a c → b = c := by
    intro a b c hab
    have surj : Function.Surjective (op a) := by
      intro z
      exact ⟨op z (op (op a z) a), (h z a).symm⟩
    exact ((Finite.surjective_iff_bijective.mp surj).1 hab)
  have h12 : c1 ≠ c2 := by
    intro e
    apply hx1
    exact cancel x x c1 (hc1.trans (e.trans hc2.symm))
  have h23 : c2 ≠ c3 := by
    intro e
    apply h12
    exact cancel x c1 c2 (hc2.trans (e.trans hc3.symm))
  have h13 : c1 ≠ c3 := by
    intro e
    apply hx2
    exact cancel x x c2 (hc1.trans (e.trans hc3.symm))
  exact ⟨h12, h13, h23⟩

private theorem trace_one
    {α : Type u} (op : α → α → α) {x c1 c2 c3 q s t : α}
    (hq : q ≠ x ∧ q ≠ c1 ∧ q ≠ c2 ∧ q ≠ c3)
    (fresh : FirstReturn.FreshOutsideSix x c1 c2 c3 q s t)
    (step : op x q = t) :
    FirstReturn.D4Trace op x c1 c2 c3 q 1 := by
  rcases hq with ⟨hq0, hq1, hq2, hq3⟩
  rcases fresh with ⟨ht0, ht1, ht2, ht3, htq, hts⟩
  refine ⟨?_, ?_⟩
  · intro i hi
    interval_cases i
    · simpa [FirstReturn.orbitPoint] using And.intro hq0 (And.intro hq1 (And.intro hq2 hq3))
    · simpa [FirstReturn.orbitPoint, step] using And.intro ht0 (And.intro ht1 (And.intro ht2 ht3))
  · intro i hi j hj hij
    interval_cases i <;> interval_cases j
    all_goals try rfl
    · exact False.elim (htq (by simpa [FirstReturn.orbitPoint, step] using hij.symm))
    · exact False.elim (htq (by simpa [FirstReturn.orbitPoint, step] using hij))

private theorem trace_two
    {α : Type u} (op : α → α → α) {x c1 c2 c3 q s t : α}
    (hq : q ≠ x ∧ q ≠ c1 ∧ q ≠ c2 ∧ q ≠ c3)
    (hs : s ≠ x ∧ s ≠ c1 ∧ s ≠ c2 ∧ s ≠ c3 ∧ s ≠ q)
    (fresh : FirstReturn.FreshOutsideSix x c1 c2 c3 q s t)
    (q_to_s : op x q = s) (step : op x s = t) :
    FirstReturn.D4Trace op x c1 c2 c3 q 2 := by
  rcases hq with ⟨hq0, hq1, hq2, hq3⟩
  rcases hs with ⟨hs0, hs1, hs2, hs3, hsq⟩
  rcases fresh with ⟨ht0, ht1, ht2, ht3, htq, hts⟩
  refine ⟨?_, ?_⟩
  · intro i hi
    interval_cases i
    · simpa [FirstReturn.orbitPoint] using And.intro hq0 (And.intro hq1 (And.intro hq2 hq3))
    · simpa [FirstReturn.orbitPoint, q_to_s] using And.intro hs0 (And.intro hs1 (And.intro hs2 hs3))
    · simpa [FirstReturn.orbitPoint, q_to_s, step] using And.intro ht0 (And.intro ht1 (And.intro ht2 ht3))
  · intro i hi j hj hij
    interval_cases i <;> interval_cases j
    all_goals try rfl
    · exact False.elim (hsq (by simpa [FirstReturn.orbitPoint, q_to_s] using hij.symm))
    · exact False.elim (htq (by simpa [FirstReturn.orbitPoint, q_to_s, step] using hij.symm))
    · exact False.elim (hsq (by simpa [FirstReturn.orbitPoint, q_to_s] using hij))
    · exact False.elim (hts (by simpa [FirstReturn.orbitPoint, q_to_s, step] using hij.symm))
    · exact False.elim (htq (by simpa [FirstReturn.orbitPoint, q_to_s, step] using hij))
    · exact False.elim (hts (by simpa [FirstReturn.orbitPoint, q_to_s, step] using hij))

private theorem trace_zero
    {α : Type u} (op : α → α → α) {x c1 c2 c3 q s t : α}
    (fresh : FirstReturn.FreshOutsideSix x c1 c2 c3 q s t) :
    FirstReturn.D4Trace op x c1 c2 c3 t 0 := by
  exact ⟨fun i hi => by
    interval_cases i
    exact ⟨fresh.1, fresh.2.1, fresh.2.2.1, fresh.2.2.2.1⟩,
    fun i hi j hj hij => by omega⟩

set_option linter.style.haveILetI false in
theorem _root_.solution
    {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op)
    (x c1 c2 c3 : α)
    (hc1 : op x x = c1) (hc2 : op x c1 = c2) (hc3 : op x c2 = c3)
    (hcloses : op x c3 = x)
    (hx_ne_c1 : x ≠ c1) (hx_ne_c2 : x ≠ c2) (hx_ne_c3 : x ≠ c3)
    (a b : α)
    (ha : InLeftOrbit op x a) (hb : InLeftOrbit op x b)
    (hab : a ≠ b) (hcollision : op a x = op b x) :
    Nonempty (FirstReturn.D4FirstReturnPacket op x c1 c2 c3) ∨
      HasFixerAt op x := by
  rcases FiniteMagmaE677.period_four_orbit_right_collision_gives_seventh_element_or_fixer op h x c1 c2 c3 hc1 hc2 hc3 hcloses
      hx_ne_c1 hx_ne_c2 hx_ne_c3 a b ha hb hab hcollision with hg | hfix
  · have growth := hg
    rcases hg with ⟨hqcol, hqpre, hqret, hqx, hq1, hq2, hq3, branch⟩
    rcases c12_ne op h hc1 hc2 hc3 hx_ne_c1 hx_ne_c2 with
      ⟨hc12, hc13, hc23⟩
    let packet : FirstReturn.D4Distinguished op x c1 c2 c3 :=
      ⟨hc1, hc2, hc3, hcloses, hx_ne_c1, hx_ne_c2, hx_ne_c3,
        hc12, hc13, hc23, hqcol, hqpre, hqret, hqx, hq1, hq2, hq3⟩
    have init : Nonempty (FirstReturn.D4Initialization op x c1 c2 c3) := by
      rcases FirstReturn.tagged_of_growth op h packet growth with start | start
      · rcases start.trace_start with fresh | ⟨contact, fresh⟩
        · exact ⟨⟨packet, .rSeedQThroughOne start fresh
            (trace_one op ⟨hqx, hq1, hq2, hq3⟩ fresh rfl)⟩⟩
        · exact ⟨⟨packet, .rSeedQThroughTwo start contact fresh
            (trace_two op ⟨hqx, hq1, hq2, hq3⟩
              ⟨start.r_ne_x, start.r_ne_c1, start.r_ne_c2, start.r_ne_c3,
                start.r_ne_q⟩ fresh contact rfl)⟩⟩
      · rcases start.trace_start with fresh | ⟨contact, fresh⟩ | ⟨contact, swap, fresh, bridge⟩
        · exact ⟨⟨packet, .sSeedQThroughOne start fresh
            (trace_one op ⟨hqx, hq1, hq2, hq3⟩ fresh rfl)⟩⟩
        · exact ⟨⟨packet, .sSeedQThroughTwo start contact fresh
            (trace_two op ⟨hqx, hq1, hq2, hq3⟩
              ⟨start.s_ne_x, start.s_ne_c1, start.s_ne_c2, start.s_ne_c3,
                start.s_ne_q⟩ fresh contact rfl)⟩⟩
        · exact ⟨⟨packet, .sSwapSeedT start contact swap fresh
            (trace_zero op fresh) bridge⟩⟩
    rcases init with ⟨init⟩
    exact Or.inl ⟨FirstReturn.e677_firstReturnReduction h init⟩
  · exact Or.inr hfix

end FiniteMagmaE677
