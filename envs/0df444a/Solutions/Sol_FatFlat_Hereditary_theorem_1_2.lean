-- Prove2me | solution 1 for FatFlat.Hereditary.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:59:07.145818+00:00
-- url     : https://prove2.me/submissions/f270d607-802c-4405-87dd-0c0e26a94d22

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Classes
import Theorems.Thm_FatFlat_Hereditary_theorem_1_3
import Theorems.Thm_FatFlat_Hereditary_lemma_5_1
import Theorems.Thm_FatFlat_Hereditary_lemma_7_1
import Theorems.Thm_FatFlat_Hereditary_lemma_6_1

section
set_option autoImplicit false

namespace FatFlat.Dev.Emb
open SparseDisc

/-- subdivision with constant `k` -/
noncomputable abbrev SD {W : Type} (G : SimpleGraph W) (k : ℕ) :=
  SparseDisc.subdivide G (fun _ => k)

section adj
variable {W : Type} (G : SimpleGraph W) (k : ℕ)

lemma SD_adj_inl_inl (u v : W) : ¬ (SD G k).Adj (Sum.inl u) (Sum.inl v) := by
  simp [SD, SparseDisc.subdivide, SimpleGraph.fromRel_adj]

lemma SD_adj_inl_inr (u : W) (e : G.edgeSet) (i : Fin (k + 1)) :
    (SD G k).Adj (Sum.inl u) (Sum.inr ⟨e, i⟩) ↔
      (u = (Quot.out (e : Sym2 W)).1 ∧ i.val = 0) ∨ (u = (Quot.out (e : Sym2 W)).2 ∧ i.val = k) := by
  simp [SD, SparseDisc.subdivide, SimpleGraph.fromRel_adj]

lemma SD_adj_inr_inr (e e' : G.edgeSet) (i : Fin (k + 1)) (j : Fin (k + 1)) :
    (SD G k).Adj (Sum.inr ⟨e, i⟩) (Sum.inr ⟨e', j⟩) ↔
      e = e' ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  simp [SD, SparseDisc.subdivide, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact ⟨h.1, Or.inl h.2⟩
    · exact ⟨h.1.symm, Or.inr h.2⟩
  · rintro ⟨rfl, h⟩
    refine ⟨fun _ hij => ?_, ?_⟩
    · subst hij; omega
    · rcases h with h | h
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr ⟨rfl, h⟩

lemma out_eq (e : Sym2 W) : s((Quot.out e).1, (Quot.out e).2) = e := Quot.out_eq e

end adj


section functor
variable {W W' : Type} {H : SimpleGraph W} {H' : SimpleGraph W'}

end functor

section web
open FatFlat.Hereditary

variable {W W' : Type} {H : SimpleGraph W} {H' : SimpleGraph W'}

end web
end FatFlat.Dev.Emb
end

section
set_option autoImplicit false

namespace FatFlat.Dev.T12
open FatFlat.Hereditary

section metric
variable {V : Type} (G : SimpleGraph V)

lemma ed_mono {s t : Set V} (hst : s ⊆ t) {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    (G.induce t).edist ⟨x, hst hx⟩ ⟨y, hst hy⟩ ≤ (G.induce s).edist ⟨x, hx⟩ ⟨y, hy⟩ := by
  by_cases hr : (G.induce s).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    rw [← hp]
    have h := SimpleGraph.edist_le (p.map (SimpleGraph.induceHomOfLE G hst).toHom)
    rw [SimpleGraph.Walk.length_map] at h
    exact h
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]; exact le_top

lemma ed_adj {t : Set V} {x y : V} (hx : x ∈ t) (hy : y ∈ t) (h : G.Adj x y) :
    (G.induce t).edist ⟨x, hx⟩ ⟨y, hy⟩ ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  left; simpa using h

lemma dist_step (N A Bs : Set V) (hA : A ⊆ N) (hB : Bs ⊆ N) (c u w cs v : V)
    (hc : c ∈ A) (hu : u ∈ A) (hw : w ∈ Bs) (hcs : cs ∈ Bs) (hv : v ∈ Bs) (a b : ℕ∞)
    (h1 : (G.induce A).edist ⟨c, hc⟩ ⟨u, hu⟩ ≤ a) (hadj : G.Adj u w)
    (h2 : (G.induce Bs).edist ⟨cs, hcs⟩ ⟨w, hw⟩ ≤ b)
    (h3 : (G.induce Bs).edist ⟨cs, hcs⟩ ⟨v, hv⟩ ≤ b) :
    (G.induce N).edist ⟨c, hA hc⟩ ⟨v, hB hv⟩ ≤ a + 1 + (b + b) := by
  have e1 := (ed_mono G hA hc hu).trans h1
  have e2 := ed_adj G (hA hu) (hB hw) hadj
  have e3 : (G.induce N).edist ⟨w, hB hw⟩ ⟨cs, hB hcs⟩ ≤ b := by
    rw [SimpleGraph.edist_comm]; exact (ed_mono G hB hcs hw).trans h2
  have e4 := (ed_mono G hB hcs hv).trans h3
  have t1 := SimpleGraph.edist_triangle (G := G.induce N) (u := ⟨c, hA hc⟩) (v := ⟨u, hA hu⟩)
    (w := ⟨v, hB hv⟩)
  have t2 := SimpleGraph.edist_triangle (G := G.induce N) (u := ⟨u, hA hu⟩) (v := ⟨w, hB hw⟩)
    (w := ⟨v, hB hv⟩)
  have t3 := SimpleGraph.edist_triangle (G := G.induce N) (u := ⟨w, hB hw⟩) (v := ⟨cs, hB hcs⟩)
    (w := ⟨v, hB hv⟩)
  calc _ ≤ _ := t1
    _ ≤ a + (1 + (b + b)) := add_le_add e1 (t2.trans (add_le_add e2 (t3.trans (add_le_add e3 e4))))
    _ = _ := by ring

end metric

open MISInducedMinor in
/-- composition of an induced-minor model of `S` in `G` with a star-shaped model of `H` in `S` -/
lemma compose {W U V : Type} (H : SimpleGraph W) (S : SimpleGraph U) (G : SimpleGraph V)
    (T : W → Set U) (hne : ∀ w, (T w).Nonempty)
    (hdisj : ∀ w w', w ≠ w' → Disjoint (T w) (T w'))
    (hstar : ∀ w, ∃ s0 ∈ T w, ∀ s ∈ T w, s = s0 ∨ S.Adj s0 s)
    (hadj : ∀ w w', w ≠ w' → ((∃ s ∈ T w, ∃ s' ∈ T w', S.Adj s s') ↔ H.Adj w w'))
    (M : InducedMinorModel S G) (ρ : ℕ) (hρ : ∀ s, RadiusLE G (M.B s) ρ) :
    ∃ M' : InducedMinorModel H G, ∀ w, RadiusLE G (M'.B w) (3 * ρ + 1) := by
  let B' : W → Set V := fun w => ⋃ s ∈ T w, M.B s
  have memB : ∀ w x, x ∈ B' w ↔ ∃ s ∈ T w, x ∈ M.B s := by
    intro w x; simp [B']
  have sub : ∀ w s, s ∈ T w → M.B s ⊆ B' w := fun w s hs x hx => (memB w x).2 ⟨s, hs, hx⟩
  have rad : ∀ w, ∃ (c : V) (hc : c ∈ B' w), ∀ (v : V) (hv : v ∈ B' w),
      (G.induce (B' w)).edist ⟨c, hc⟩ ⟨v, hv⟩ ≤ ((3 * ρ + 1 : ℕ) : ℕ∞) := by
    intro w
    obtain ⟨s0, hs0, hst⟩ := hstar w
    obtain ⟨⟨c, hc⟩, hcrad⟩ := hρ s0
    refine ⟨c, sub w s0 hs0 hc, ?_⟩
    intro v hv
    obtain ⟨s, hs, hvs⟩ := (memB w v).1 hv
    rcases hst s hs with rfl | hadj0
    · refine (ed_mono G (sub w s hs) hc hvs).trans ?_
      refine (hcrad ⟨v, hvs⟩).trans ?_
      exact_mod_cast (by omega : ρ ≤ 3 * ρ + 1)
    · have hne : s0 ≠ s := hadj0.ne
      obtain ⟨u, hu, w', hw', huw⟩ := (M.adj_iff s0 s hne).2 hadj0
      obtain ⟨⟨cs, hcs⟩, hcsrad⟩ := hρ s
      have := dist_step G (B' w) (M.B s0) (M.B s) (sub w s0 hs0) (sub w s hs) c u w' cs v hc hu
        hw' hcs hvs (ρ : ℕ∞) (ρ : ℕ∞) (hcrad ⟨u, hu⟩) huw (hcsrad ⟨w', hw'⟩) (hcsrad ⟨v, hvs⟩)
      refine this.trans (le_of_eq ?_)
      push_cast; ring
  refine ⟨⟨B', ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro w
    obtain ⟨s, hs⟩ := hne w
    obtain ⟨x, hx⟩ := M.nonempty s
    exact ⟨x, (memB w x).2 ⟨s, hs, hx⟩⟩
  · intro w w' hww
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    obtain ⟨s, hs, hxs⟩ := (memB w x).1 hx
    obtain ⟨s', hs', hxs'⟩ := (memB w' x).1 hx'
    have hss : s ≠ s' := by
      rintro rfl
      exact Set.disjoint_left.1 (hdisj w w' hww) hs hs'
    exact Set.disjoint_left.1 (M.disjoint hss) hxs hxs'
  · intro w
    obtain ⟨c, hc, h⟩ := rad w
    have hreach : ∀ v : ↥(B' w), (G.induce (B' w)).Reachable ⟨c, hc⟩ v := fun v =>
      SimpleGraph.reachable_of_edist_ne_top
        (ne_top_of_le_ne_top (ENat.natCast_ne_top _) (h v.1 v.2))
    have hnon : Nonempty ↥(B' w) := ⟨⟨c, hc⟩⟩
    exact @SimpleGraph.Connected.mk _ _ (fun a b => (hreach a).symm.trans (hreach b)) hnon
  · intro w w' hww
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      obtain ⟨s, hs, hxs⟩ := (memB w x).1 hx
      obtain ⟨s', hs', hys⟩ := (memB w' y).1 hy
      have hss : s ≠ s' := by
        rintro rfl
        exact Set.disjoint_left.1 (hdisj w w' hww) hs hs'
      have := (M.adj_iff s s' hss).1 ⟨x, hxs, y, hys, hxy⟩
      exact (hadj w w' hww).1 ⟨s, hs, s', hs', this⟩
    · intro h
      obtain ⟨s, hs, s', hs', hss⟩ := (hadj w w' hww).2 h
      obtain ⟨x, hx, y, hy, hxy⟩ := (M.adj_iff s s' hss.ne).2 hss
      exact ⟨x, sub w s hs hx, y, sub w' s' hs' hy, hxy⟩
  · intro w
    obtain ⟨c, hc, h⟩ := rad w
    exact ⟨⟨c, hc⟩, fun v => h v.1 v.2⟩


section onesub
variable {W : Type} (G : SimpleGraph W)

lemma oS_inl_inr (v : W) (e : G.edgeSet) (z : Fin (0 + 1)) :
    (oneSubdivision G).Adj (Sum.inl v) (Sum.inr ⟨e, z⟩) ↔ v ∈ (e : Sym2 W) := by
  have h := FatFlat.Dev.Emb.SD_adj_inl_inr G 0 v e z
  have hz : z.val = 0 := by omega
  have hq := FatFlat.Dev.Emb.out_eq (e : Sym2 W)
  change (FatFlat.Dev.Emb.SD G 0).Adj _ _ ↔ _
  rw [h, hz]
  simp only [and_true]
  conv_rhs => rw [← hq]
  simp [Sym2.mem_iff]

lemma oS_inl_inl (u v : W) : ¬ (oneSubdivision G).Adj (Sum.inl u) (Sum.inl v) :=
  FatFlat.Dev.Emb.SD_adj_inl_inl G 0 u v

lemma oS_inr_inr (e e' : G.edgeSet) (i j : Fin (0 + 1)) :
    ¬ (oneSubdivision G).Adj (Sum.inr ⟨e, i⟩) (Sum.inr ⟨e', j⟩) := by
  intro h
  have h' := (FatFlat.Dev.Emb.SD_adj_inr_inr G 0 e e' i j).1 h
  omega

end onesub

section branch
variable {n : ℕ} (H : SimpleGraph (Fin n))

/-- branch set of `i` in the 1-subdivision of `K_{n+1}` -/
def T (i : Fin n) : Set (Fin (n + 1) ⊕ (Σ _ : (⊤ : SimpleGraph (Fin (n + 1))).edgeSet, Fin (0 + 1))) :=
  {s | s = Sum.inl i.castSucc ∨ ∃ (e : (⊤ : SimpleGraph (Fin (n + 1))).edgeSet) (z : Fin (0 + 1))
      (j : Fin n), s = Sum.inr ⟨e, z⟩ ∧ (e : Sym2 (Fin (n + 1))) = s(i.castSucc, j.castSucc) ∧
        i < j ∧ H.Adj i j}

lemma T_nonempty (i : Fin n) : (T H i).Nonempty := ⟨Sum.inl i.castSucc, Or.inl rfl⟩

lemma T_disj (i i' : Fin n) (hii : i ≠ i') : Disjoint (T H i) (T H i') := by
  rw [Set.disjoint_left]
  intro s hs hs'
  rcases hs with rfl | ⟨e, z, j, rfl, he, hij, hadj⟩
  · rcases hs' with h | ⟨e', z', j', h, _⟩
    · exact hii (Fin.castSucc_injective _ (Sum.inl_injective h))
    · exact Sum.inl_ne_inr h
  · rcases hs' with h | ⟨e', z', j', h, he', hij', hadj'⟩
    · exact Sum.inr_ne_inl h
    · have hee : e = e' := by
        have := Sum.inr_injective h
        exact (Sigma.mk.inj this).1
      subst hee
      rw [he] at he'
      rcases Sym2.eq_iff.1 he' with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hii (Fin.castSucc_injective _ h1)
      · have a1 := Fin.castSucc_injective _ h1
        have a2 := Fin.castSucc_injective _ h2
        omega

lemma T_star (i : Fin n) : ∃ s0 ∈ T H i, ∀ s ∈ T H i, s = s0 ∨
    (oneSubdivision (⊤ : SimpleGraph (Fin (n + 1)))).Adj s0 s := by
  refine ⟨Sum.inl i.castSucc, Or.inl rfl, ?_⟩
  rintro s (rfl | ⟨e, z, j, rfl, he, _⟩)
  · exact Or.inl rfl
  · right
    rw [oS_inl_inr, he]
    simp

lemma T_adj (i j : Fin n) (hij : i ≠ j) :
    (∃ s ∈ T H i, ∃ s' ∈ T H j,
      (oneSubdivision (⊤ : SimpleGraph (Fin (n + 1)))).Adj s s') ↔ H.Adj i j := by
  constructor
  · rintro ⟨s, hs, s', hs', hadj⟩
    rcases hs with rfl | ⟨e, z, k, rfl, he, _, hk⟩
    · rcases hs' with rfl | ⟨e', z', k', rfl, he', _, hk'⟩
      · exact absurd hadj (oS_inl_inl _ _ _)
      · rw [oS_inl_inr, he'] at hadj
        simp only [Sym2.mem_iff] at hadj
        rcases hadj with h | h
        · exact absurd (Fin.castSucc_injective _ h) hij
        · rw [Fin.castSucc_injective _ h]; exact hk'.symm
    · rcases hs' with rfl | ⟨e', z', k', rfl, he', _, hk'⟩
      · rw [SimpleGraph.adj_comm, oS_inl_inr, he] at hadj
        simp only [Sym2.mem_iff] at hadj
        rcases hadj with h | h
        · exact absurd (Fin.castSucc_injective _ h).symm hij
        · have := Fin.castSucc_injective _ h
          subst this; exact hk
      · exact absurd hadj (oS_inr_inr _ _ _ _ _)
  · intro h
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · refine ⟨Sum.inr ⟨⟨s(i.castSucc, j.castSucc), ?_⟩, 0⟩, Or.inr ⟨_, 0, j, rfl, rfl, hlt, h⟩,
        Sum.inl j.castSucc, Or.inl rfl, ?_⟩
      · simpa using hij
      · rw [SimpleGraph.adj_comm, oS_inl_inr]; simp
    · refine ⟨Sum.inl i.castSucc, Or.inl rfl,
        Sum.inr ⟨⟨s(j.castSucc, i.castSucc), ?_⟩, 0⟩, Or.inr ⟨_, 0, i, rfl, rfl, hgt, h.symm⟩, ?_⟩
      · simpa using hij.symm
      · rw [oS_inl_inr]; simp

end branch

lemma drill_mono {V : Type} (G : SimpleGraph V) (α α' β : ℕ) (hα : α ≤ α') (N : ℕ → ℕ) (s : ℕ)
    (h : IsDrillFlat G α' β N s) : IsDrillFlat G α β N s := by
  intro m A hA
  obtain ⟨B, hB, hc, X, hX, hsc⟩ := h m A hA
  refine ⟨B, hB, hc, X, hX, ?_⟩
  intro a b ha hb hab
  exact lt_of_le_of_lt (by exact_mod_cast hα) (hsc a b ha hb hab)

end FatFlat.Dev.T12

namespace FatFlat.Hereditary
open FatFlat.Dev.T12 in
theorem chk_theorem_1_2 (C : GraphClass) (hC : IsHereditary C) :
    List.TFAE [ISMF C, FSMF C, DrillFlat C, PatternFree C] := by
  tfae_have 1 → 3 := by
    intro hI
    obtain ⟨c, hc⟩ := FatFlat.Hereditary.theorem_1_3
    refine ⟨37, by norm_num, ?_⟩
    intro α hα
    obtain ⟨n, H, hH⟩ := hI (9 * α + 1)
    obtain ⟨N, hN, -⟩ := hc (n + 1) α (Nat.succ_pos n) hα
    refine ⟨N, (n + 1) * α, ?_⟩
    intro V _ G hG
    have hfree : ¬ IsShallowInducedMinor (oneSubdivision (⊤ : SimpleGraph (Fin (n + 1)))) G
        (3 * α) := by
      rintro ⟨M, hM⟩
      obtain ⟨M', hM'⟩ := compose H _ G (T H) (T_nonempty H) (T_disj H) (T_star H)
        (T_adj H) M (3 * α) hM
      exact hH V G hG ⟨M', fun w => by
        have := hM' w
        rwa [show 3 * (3 * α) + 1 = 9 * α + 1 by ring] at this⟩
    exact drill_mono G α (2 * α) 37 (by omega) N _ (hN V G hfree)
  tfae_have 3 → 2 := FatFlat.Hereditary.lemma_5_1 C
  tfae_have 2 → 4 := FatFlat.Hereditary.lemma_7_1 C hC
  tfae_have 4 → 1 := FatFlat.Hereditary.lemma_6_1 C
  tfae_finish
end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_theorem_1_2 := @FatFlat.Hereditary.chk_theorem_1_2
