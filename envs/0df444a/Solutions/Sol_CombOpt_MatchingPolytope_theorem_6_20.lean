-- Prove2me | solution 1 for CombOpt.MatchingPolytope.theorem_6_20
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T12:11:05.449796+00:00
-- url     : https://prove2.me/submissions/5c8aa165-945e-48bb-8691-afcf09478661

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsMatching
import Definitions.Def_CombOpt_MatchingPolytope_charVec
import Definitions.Def_CombOpt_MatchingPolytope_Graph_matchingPolytope
import Definitions.Def_CombOpt_MatchingPolytope_Graph_cut
import Definitions.Def_CombOpt_MatchingPolytope_Graph_gamma
import Definitions.Def_CombOpt_MatchingPolytope_Graph_system67
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsPerfectMatching
import Definitions.Def_CombOpt_MatchingPolytope_Graph_system63
import Theorems.Thm_CombOpt_MatchingPolytope_theorem_6_3

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CombOpt.MatchingPolytope.P63b4

open CombOpt.MatchingPolytope Classical

variable {V E : Type*} [Fintype V] [Fintype E]

theorem ends_eq (G : Graph V E) (hG : G.IsLoopless) (e : E) :
    ∃ a b : V, a ≠ b ∧ G.ends e = s(a, b) := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  refine ⟨a, b, ?_, hab.symm⟩
  intro h
  apply hG e
  rw [← hab]
  exact (Sym2.mk_isDiag_iff).2 h

theorem sum_charVec (M T : Finset E) :
    ∑ e ∈ T, charVec M e = ((T.filter (· ∈ M)).card : ℝ) := by
  simp only [charVec]
  rw [Finset.sum_boole]

theorem system67_convex (G : Graph V E) : Convex ℝ G.system67 := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨fun v => ?_, fun S h3 hodd => ?_, fun e => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := hx1 v; have := hy1 v
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := hx2 S h3 hodd; have h2 := hy2 S h3 hodd
    have : a * (∑ e ∈ G.gamma S, x e) + b * (∑ e ∈ G.gamma S, y e)
        ≤ a * (((S.card : ℝ) - 1) / 2) + b * (((S.card : ℝ) - 1) / 2) := by
      have := mul_le_mul_of_nonneg_left h1 ha
      have := mul_le_mul_of_nonneg_left h2 hb
      linarith
    calc _ ≤ _ := this
      _ = _ := by rw [← add_mul, hab, one_mul]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx3 e; have := hy3 e
    positivity

theorem charVec_mem_system67 (G : Graph V E) (hG : G.IsLoopless) (M : Finset E)
    (hM : G.IsMatching M) : charVec M ∈ G.system67 := by
  refine ⟨fun v => ?_, fun S h3 hodd => ?_, fun e => ?_⟩
  · rw [sum_charVec]
    have hsub : (G.cut {v}).filter (· ∈ M) ⊆ M.filter (fun e => v ∈ G.ends e) := by
      intro e he
      simp only [Finset.mem_filter, Graph.cut, Finset.mem_univ, true_and,
        Finset.mem_singleton] at he ⊢
      obtain ⟨⟨a, ha, rfl⟩, _⟩ := he.1
      exact ⟨he.2, ha⟩
    have := (Finset.card_le_card hsub).trans (hM v)
    exact_mod_cast this
  · rw [sum_charVec]
    set T := (G.gamma S).filter (· ∈ M) with hT
    -- double counting: 2 |T| ≤ |S|
    have hdc : ∑ e ∈ T, (S.filter (fun v => v ∈ G.ends e)).card
        = ∑ v ∈ S, (T.filter (fun e => v ∈ G.ends e)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have hl : ∀ e ∈ T, (S.filter (fun v => v ∈ G.ends e)).card = 2 := by
      intro e he
      simp only [hT, Finset.mem_filter, Graph.gamma, Finset.mem_univ, true_and] at he
      obtain ⟨a, b, hne, hab⟩ := ends_eq G hG e
      have ha : a ∈ S := he.1 a (by rw [hab]; exact Sym2.mem_mk_left a b)
      have hb : b ∈ S := he.1 b (by rw [hab]; exact Sym2.mem_mk_right a b)
      have : S.filter (fun v => v ∈ G.ends e) = {a, b} := by
        ext w
        simp only [Finset.mem_filter, hab, Sym2.mem_iff, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨ha, Or.inl rfl⟩
          · exact ⟨hb, Or.inr rfl⟩
      rw [this, Finset.card_pair hne]
    have hr : ∀ v ∈ S, (T.filter (fun e => v ∈ G.ends e)).card ≤ 1 := by
      intro v _
      refine le_trans (Finset.card_le_card ?_) (hM v)
      intro e he
      simp only [hT, Finset.mem_filter] at he ⊢
      exact ⟨he.1.2, he.2⟩
    have h2 : 2 * T.card ≤ S.card := by
      have e1 : ∑ e ∈ T, (S.filter (fun v => v ∈ G.ends e)).card = 2 * T.card := by
        rw [Finset.sum_congr rfl hl, Finset.sum_const, smul_eq_mul, mul_comm]
      have e2 : ∑ v ∈ S, (T.filter (fun e => v ∈ G.ends e)).card ≤ S.card := by
        calc _ ≤ ∑ _v ∈ S, 1 := Finset.sum_le_sum hr
          _ = S.card := by simp
      omega
    obtain ⟨k, hk⟩ := hodd
    have h2' : 2 * T.card ≤ 2 * k := by omega
    have : (T.card : ℝ) ≤ k := by exact_mod_cast (by omega : T.card ≤ k)
    rw [hk]; push_cast
    linarith
  · simp only [charVec]; split_ifs <;> norm_num

/-- `M(G) ⊆ (6.7)`. -/
theorem matchingPolytope_subset (G : Graph V E) (hG : G.IsLoopless) :
    G.matchingPolytope ⊆ G.system67 := by
  apply convexHull_min _ (system67_convex G)
  rintro _ ⟨M, hM, rfl⟩
  exact charVec_mem_system67 G hG M hM

/-- The doubled graph: two copies of `G` plus an edge `v v'` for each node. -/
def dbl (G : Graph V E) : Graph (V ⊕ V) (E ⊕ E ⊕ V) :=
  ⟨Sum.elim (fun e => (G.ends e).map Sum.inl)
    (Sum.elim (fun e => (G.ends e).map Sum.inr) (fun v => s(Sum.inl v, Sum.inr v)))⟩

theorem dbl_loopless (G : Graph V E) (hG : G.IsLoopless) : (dbl G).IsLoopless := by
  rintro (e | e | v)
  · obtain ⟨a, b, hne, hab⟩ := ends_eq G hG e
    simp [dbl, hab, hne]
  · obtain ⟨a, b, hne, hab⟩ := ends_eq G hG e
    simp [dbl, hab, hne]
  · simp [dbl]

/-- The lifted vector on the doubled graph. -/
noncomputable def lift (G : Graph V E) (x : E → ℝ) : E ⊕ E ⊕ V → ℝ :=
  Sum.elim x (Sum.elim x (fun v => 1 - ∑ e ∈ G.cut {v}, x e))

/-- Restriction of a perfect matching of `dbl G` to the first copy is a matching of `G`. -/
theorem restrict_isMatching (G : Graph V E) (M : Finset (E ⊕ E ⊕ V))
    (hM : (dbl G).IsMatching M) :
    G.IsMatching (Finset.univ.filter (fun e => Sum.inl e ∈ M)) := by
  intro v
  have h := hM (Sum.inl v)
  refine le_trans ?_ h
  refine Finset.card_le_card_of_injOn Sum.inl ?_ (Sum.inl_injective.injOn)
  intro e he
  simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_setOf_eq] at he ⊢
  refine ⟨he.1, ?_⟩
  simp only [dbl, Sum.elim_inl, Sym2.mem_map, Sum.inl.injEq, exists_eq_right]
  exact he.2

/-- Assembly of `⊇` from the perfect matching polytope theorem for `dbl G` and the
membership of the lifted vector in (6.3) of `dbl G`. -/
theorem system67_subset_of (G : Graph V E)
    (h63 : convexHull ℝ {y | ∃ M : Finset (E ⊕ E ⊕ V), (dbl G).IsPerfectMatching M ∧
        y = charVec M} = (dbl G).system63)
    (hlift : ∀ x ∈ G.system67, lift G x ∈ (dbl G).system63) :
    G.system67 ⊆ G.matchingPolytope := by
  intro x hx
  have hy := hlift x hx
  rw [← h63] at hy
  let π : ((E ⊕ E ⊕ V) → ℝ) →ₗ[ℝ] (E → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inl
  have hx' : x = π (lift G x) := by
    funext e; simp [π, lift, LinearMap.funLeft]
  rw [hx']
  have hmem : π (lift G x) ∈ π '' convexHull ℝ {y | ∃ M : Finset (E ⊕ E ⊕ V),
      (dbl G).IsPerfectMatching M ∧ y = charVec M} := ⟨_, hy, rfl⟩
  rw [LinearMap.image_convexHull] at hmem
  refine convexHull_mono ?_ hmem
  rintro _ ⟨y, ⟨M, hM, rfl⟩, rfl⟩
  refine ⟨Finset.univ.filter (fun e => Sum.inl e ∈ M), restrict_isMatching G M hM.1, ?_⟩
  funext e
  simp [π, LinearMap.funLeft, charVec]

theorem mem_cut_iff (G : Graph V E) {e : E} {a b : V} (hab : G.ends e = s(a, b))
    (A : Finset V) : e ∈ G.cut A ↔ (a ∈ A ∨ b ∈ A) ∧ (a ∉ A ∨ b ∉ A) := by
  simp [Graph.cut, hab, Sym2.mem_iff, or_and_right, exists_or]

theorem mem_gamma_iff (G : Graph V E) {e : E} {a b : V} (hab : G.ends e = s(a, b))
    (S : Finset V) : e ∈ G.gamma S ↔ a ∈ S ∧ b ∈ S := by
  simp [Graph.gamma, hab, Sym2.mem_iff, or_imp, forall_and]

theorem sum_mem_eq (T : Finset E) (x : E → ℝ) :
    ∑ e ∈ T, x e = ∑ e, x e * (if e ∈ T then (1 : ℝ) else 0) := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Per-edge counting bound. -/
theorem edge_bound (G : Graph V E) (e : E) (A B : Finset V) :
    ∑ v ∈ A \ B, (if e ∈ G.cut {v} then (1 : ℝ) else 0) ≤
      (if e ∈ G.cut A then (1 : ℝ) else 0) + (if e ∈ G.cut B then (1 : ℝ) else 0) +
        2 * (if e ∈ G.gamma (A \ B) then (1 : ℝ) else 0) := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  have hab' : G.ends e = s(a, b) := hab.symm
  have h1 : ∑ v ∈ A \ B, (if e ∈ G.cut {v} then (1 : ℝ) else 0) ≤
      ∑ v ∈ A \ B, ((if a = v then (1 : ℝ) else 0) + (if b = v then (1 : ℝ) else 0)) := by
    refine Finset.sum_le_sum fun v _ => ?_
    simp only [mem_cut_iff G hab', Finset.mem_singleton]
    split_ifs <;> simp_all
  refine h1.trans (le_of_eq_of_le (by rw [Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq]) ?_)
  simp only [mem_cut_iff G hab', mem_gamma_iff G hab', Finset.mem_sdiff]
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> by_cases ha' : a ∈ B <;>
    by_cases hb' : b ∈ B <;> simp [ha, hb, ha', hb'] <;> norm_num

theorem sum_deg_le (G : Graph V E) (x : E → ℝ) (hx : ∀ e, 0 ≤ x e) (A B : Finset V) :
    ∑ v ∈ A \ B, ∑ e ∈ G.cut {v}, x e ≤
      ∑ e ∈ G.cut A, x e + ∑ e ∈ G.cut B, x e + 2 * ∑ e ∈ G.gamma (A \ B), x e := by
  have h1 : ∑ v ∈ A \ B, ∑ e ∈ G.cut {v}, x e =
      ∑ e, x e * ∑ v ∈ A \ B, (if e ∈ G.cut {v} then (1 : ℝ) else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => sum_mem_eq _ _
  rw [h1, sum_mem_eq (G.cut A), sum_mem_eq (G.cut B), sum_mem_eq (G.gamma (A \ B)),
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have := mul_le_mul_of_nonneg_left (edge_bound G e A B) (hx e)
  linarith

theorem key (G : Graph V E) (hG : G.IsLoopless) (x : E → ℝ) (hx : x ∈ G.system67)
    (A B : Finset V) (hodd : Odd (A \ B).card) :
    1 ≤ ∑ e ∈ G.cut A, x e + (∑ e ∈ G.cut B, x e +
      ∑ v ∈ Finset.univ.filter (fun v => (v ∈ A ∨ v ∈ B) ∧ (v ∉ A ∨ v ∉ B)),
        (1 - ∑ e ∈ G.cut {v}, x e)) := by
  obtain ⟨hdeg, h67, hnn⟩ := hx
  have hsub : A \ B ⊆ Finset.univ.filter (fun v => (v ∈ A ∨ v ∈ B) ∧ (v ∉ A ∨ v ∉ B)) := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    simp [hv.1, hv.2]
  have h2 : ∑ v ∈ A \ B, (1 - ∑ e ∈ G.cut {v}, x e) ≤
      ∑ v ∈ Finset.univ.filter (fun v => (v ∈ A ∨ v ∈ B) ∧ (v ∉ A ∨ v ∉ B)),
        (1 - ∑ e ∈ G.cut {v}, x e) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun v _ _ => by linarith [hdeg v]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at h2
  have h3 := sum_deg_le G x hnn A B
  have hg : ∑ e ∈ G.gamma (A \ B), x e ≤ (((A \ B).card : ℝ) - 1) / 2 := by
    by_cases hc : 3 ≤ (A \ B).card
    · exact h67 _ hc hodd
    · have h1 : (A \ B).card = 1 := by
        obtain ⟨k, hk⟩ := hodd; omega
      obtain ⟨s, hs⟩ := Finset.card_eq_one.1 h1
      rw [hs, Finset.card_singleton]
      have : ∑ e ∈ G.gamma {s}, x e = 0 := by
        refine Finset.sum_eq_zero fun e he => ?_
        exfalso
        obtain ⟨a, b, hne, hab⟩ := ends_eq G hG e
        rw [mem_gamma_iff G hab] at he
        simp only [Finset.mem_singleton] at he
        exact hne (he.1.trans he.2.symm)
      rw [this]; norm_num
  linarith

theorem dbl_cut_sum (G : Graph V E) (x : E → ℝ) (U : Finset (V ⊕ V)) :
    ∑ e ∈ (dbl G).cut U, lift G x e =
      ∑ e ∈ G.cut U.toLeft, x e + (∑ e ∈ G.cut U.toRight, x e +
      ∑ v ∈ Finset.univ.filter (fun v => (v ∈ U.toLeft ∨ v ∈ U.toRight) ∧
          (v ∉ U.toLeft ∨ v ∉ U.toRight)), (1 - ∑ e ∈ G.cut {v}, x e)) := by
  simp only [Graph.cut, Finset.sum_filter, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp [dbl, lift, Sym2.mem_map]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp [dbl, lift, Sym2.mem_map]
  · refine Finset.sum_congr rfl fun v _ => ?_
    simp [dbl, lift, Graph.cut, Finset.sum_filter]

theorem lift_mem_system63 (G : Graph V E) (hG : G.IsLoopless) (x : E → ℝ)
    (hx : x ∈ G.system67) : lift G x ∈ (dbl G).system63 := by
  have hx' := hx
  obtain ⟨hdeg, _, hnn⟩ := hx'
  have hcut0 : G.cut ∅ = ∅ := by ext; simp [Graph.cut]
  refine ⟨fun w => ?_, fun U h3 hU => ?_, fun e => ?_⟩
  · rw [dbl_cut_sum]
    rcases w with v | v
    · have hA : ({Sum.inl v} : Finset (V ⊕ V)).toLeft = {v} := by ext; simp
      have hB : ({Sum.inl v} : Finset (V ⊕ V)).toRight = ∅ := by ext; simp
      rw [hA, hB, hcut0, Finset.sum_filter]
      simp
    · have hA : ({Sum.inr v} : Finset (V ⊕ V)).toLeft = ∅ := by ext; simp
      have hB : ({Sum.inr v} : Finset (V ⊕ V)).toRight = {v} := by ext; simp
      rw [hA, hB, hcut0, Finset.sum_filter]
      simp
  · rw [dbl_cut_sum]
    have hcard := Finset.card_toLeft_add_card_toRight (u := U)
    have e1 := Finset.card_sdiff_add_card_inter U.toLeft U.toRight
    have e2 := Finset.card_sdiff_add_card_inter U.toRight U.toLeft
    rw [Finset.inter_comm] at e2
    by_cases hp : Odd (U.toLeft \ U.toRight).card
    · exact key G hG x hx _ _ hp
    · have hq : Odd (U.toRight \ U.toLeft).card := by
        rw [Nat.not_odd_iff_even] at hp
        obtain ⟨k, hk⟩ := hp
        obtain ⟨m, hm⟩ := hU
        exact ⟨m - k - (U.toLeft ∩ U.toRight).card, by omega⟩
      have := key G hG x hx _ _ hq
      have hf : Finset.univ.filter (fun v => (v ∈ U.toRight ∨ v ∈ U.toLeft) ∧
            (v ∉ U.toRight ∨ v ∉ U.toLeft)) =
          Finset.univ.filter (fun v => (v ∈ U.toLeft ∨ v ∈ U.toRight) ∧
            (v ∉ U.toLeft ∨ v ∉ U.toRight)) := by
        ext v; simp only [Finset.mem_filter]; tauto
      rw [hf] at this
      linarith
  · rcases e with e | e | v
    · exact hnn e
    · exact hnn e
    · simp only [lift, Sum.elim_inr]
      linarith [hdeg v]

/-- `(6.7) ⊆ M(G)` given the perfect matching polytope theorem for `dbl G`. -/
theorem system67_subset (G : Graph V E)
    (h63 : convexHull ℝ {y | ∃ M : Finset (E ⊕ E ⊕ V), (dbl G).IsPerfectMatching M ∧
        y = charVec M} = (dbl G).system63) (hG : G.IsLoopless) :
    G.system67 ⊆ G.matchingPolytope :=
  system67_subset_of G h63 fun x hx => lift_mem_system63 G hG x hx

end CombOpt.MatchingPolytope.P63b4

open CombOpt.MatchingPolytope in
/-- Edmonds' Matching Polytope Theorem (CCPS Theorem 6.20, loopless form), reduced to the
Perfect Matching Polytope Theorem 6.3 applied to the doubled graph. -/
theorem solution {V E : Type*} [Fintype V] [Fintype E] (G : CombOpt.MatchingPolytope.Graph V E)
    (hG : G.IsLoopless) :
    G.matchingPolytope = G.system67 := by
  exact Set.Subset.antisymm (P63b4.matchingPolytope_subset G hG)
    (P63b4.system67_subset G (theorem_6_3 (P63b4.dbl G) (P63b4.dbl_loopless G hG)) hG)
