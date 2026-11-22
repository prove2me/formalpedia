-- Prove2me | solution 1 for BFAlmostLinear.lemma_4_16
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-22T02:00:17.355693+00:00
-- url     : https://prove2.me/submissions/2d4583cb-a326-469e-b176-25c1e082fc03

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph_I1

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime

private theorem path_append_iff {V E : Type} (net : Network V E) (P Q : List E) {r u : V} :
    net.IsPathFrom r u (P ++ Q) ↔ ∃ z, net.IsPathFrom r z P ∧ net.IsPathFrom z u Q := by
  induction P generalizing r with
  | nil =>
    constructor
    · intro h
      exact ⟨r, rfl, h⟩
    · rintro ⟨z, hz, h⟩
      change r = z at hz
      simpa only [hz, List.nil_append] using h
  | cons a P ih =>
    change (net.tail a = r ∧ net.IsPathFrom (net.head a) u (P ++ Q)) ↔ _
    constructor
    · rintro ⟨ha, h⟩
      obtain ⟨z, hP, hQ⟩ := (ih (r := net.head a)).mp h
      exact ⟨z, ⟨ha, hP⟩, hQ⟩
    · rintro ⟨z, ⟨ha, hP⟩, hQ⟩
      exact ⟨ha, (ih (r := net.head a)).mpr ⟨z, hP, hQ⟩⟩

private theorem path_append_cons_iff {V E : Type} (net : Network V E)
    {P Q : List E} {r u : V} {a : E} :
    net.IsPathFrom r u (P ++ a :: Q) ↔
      net.IsPathFrom r (net.tail a) P ∧ net.IsPathFrom (net.head a) u Q := by
  rw [path_append_iff]
  constructor
  · rintro ⟨z, hP, hz, hQ⟩
    exact ⟨by simpa only [hz] using hP, hQ⟩
  · rintro ⟨hP, hQ⟩
    exact ⟨net.tail a, hP, rfl, hQ⟩

private theorem pathWeight_append {E : Type} (w : E → ℝ) (P Q : List E) :
    pathWeight w (P ++ Q) = pathWeight w P + pathWeight w Q := by
  simp [pathWeight, List.sum_append]

private theorem pathWeight_cons {E : Type} (w : E → ℝ) (a : E) (P : List E) :
    pathWeight w (a :: P) = w a + pathWeight w P := rfl

private theorem hops_append {V E : Type} (G : WGraph V E) (P Q : List E) :
    G.hops (P ++ Q) = G.hops P + G.hops Q := by simp [WGraph.hops]

/-- Use the last occurrence of a largest positive rank. -/
private theorem rightmost_positive_max {E : Type} (rank : E → ℕ) (P : List E)
    (hpos : ∃ a ∈ P, 0 < rank a) :
    ∃ (L : List E) (b : E) (R : List E), P = L ++ b :: R ∧ 0 < rank b ∧
      (∀ a ∈ L, rank a ≤ rank b) ∧ (∀ a ∈ R, rank a < rank b) := by
  induction P with
  | nil => simp at hpos
  | cons a P ih =>
    by_cases hrest : ∃ e ∈ P, 0 < rank e
    · obtain ⟨L, b, R, hsplit, hb, hL, hR⟩ := ih hrest
      by_cases hab : rank a ≤ rank b
      · refine ⟨a :: L, b, R, ?_, hb, ?_, hR⟩
        · simp only [List.cons_append, hsplit]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hab
          · exact hL x hx
      · have hba : rank b < rank a := Nat.lt_of_not_ge hab
        refine ⟨[], a, P, rfl, hb.trans hba, by simp, ?_⟩
        intro x hx
        rw [hsplit] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact (hL x hx).trans_lt hba
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hba
          · exact (hR x hx).trans hba
    · obtain ⟨x, hx, hxpos⟩ := hpos
      have ha : 0 < rank a := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hxpos
        · exact (hrest ⟨x, hx, hxpos⟩).elim
      refine ⟨[], a, P, rfl, ha, by simp, ?_⟩
      intro x hx
      have hn : ¬ 0 < rank x := fun hp => hrest ⟨x, hx, hp⟩
      omega

/-- The induction counts levels on the nonempty suffix that starts at a level-zero vertex. -/
private theorem unfold_from_zero {V E : Type} (G : WGraph V E) (level : V → ℕ)
    (hI2 : G.I2 level) (hI3 : G.I3Path level) (hI4 : G.I4 level) (k : ℕ) :
    ∀ (r u : V) (P : List E), level r = 0 → P ≠ [] → G.net.IsPathFrom r u P →
      (∀ x ∈ P, G.Usable x) → (∀ x ∈ P, level (G.net.tail x) ≤ k) →
      ∃ (P' : List E) (e' : E), G.net.IsPathFrom r u (P' ++ [e']) ∧
        (∀ x ∈ P' ++ [e'], G.Usable x) ∧ G.hops (P' ++ [e']) ≤ G.hops P + k ∧
        pathWeight G.w (P' ++ [e']) = pathWeight G.w P ∧
        (0 < level u → level (G.net.tail e') < level u) ∧
        (level u = 0 → level (G.net.tail e') = 0) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro r u P hr hnonempty hp hu hlevels
    cases P using List.reverseRecOn with
    | nil => exact (hnonempty rfl).elim
    | append_singleton P e =>
      have hend : G.net.head e = u := (path_append_cons_iff G.net).mp hp |>.2
      by_cases hgood : (0 < level u → level (G.net.tail e) < level u) ∧
          (level u = 0 → level (G.net.tail e) = 0)
      · exact ⟨P, e, hp, hu, Nat.le_add_right _ _, rfl, hgood⟩
      · have hbad : level u < level (G.net.tail e) := by
          by_contra! hle
          apply hgood
          constructor
          · intro hu0
            apply lt_of_le_of_ne hle
            intro heq
            have hzero := hI2 e (by simpa only [hend] using heq)
            omega
          · intro hu0
            omega
        obtain ⟨L, b, B, hsplit, hpeak, hleft, hright⟩ :=
          rightmost_positive_max (fun x => level (G.net.tail x)) (P ++ [e])
            ⟨e, List.mem_concat_self, Nat.zero_le (level u) |>.trans_lt hbad⟩
        have hpeak_le : level (G.net.tail b) ≤ k := hlevels b
          (hsplit.symm ▸ List.mem_append_cons_self)
        have hLne : L ≠ [] := by
          intro hnil
          have hP' : G.net.IsPathFrom r u (b :: B) := by simpa [hsplit, hnil] using hp
          have hbr : G.net.tail b = r := hP'.1
          simp [hbr, hr] at hpeak
        have hex : ∃ A a, L = A ++ [a] := by
          cases L using List.reverseRecOn with
          | nil => exact (hLne rfl).elim
          | append_singleton A a => exact ⟨A, a, rfl⟩
        obtain ⟨A, a, rfl⟩ := hex
        have htwo : P ++ [e] = A ++ a :: b :: B := by
          simpa only [List.append_assoc, List.singleton_append] using hsplit
        have hPab : G.net.IsPathFrom r u (A ++ a :: b :: B) := htwo ▸ hp
        obtain ⟨hA, hab⟩ := (path_append_cons_iff G.net).mp hPab
        obtain ⟨hba, hB⟩ := hab
        have huab : ∀ x ∈ A ++ a :: b :: B, G.Usable x := htwo ▸ hu
        have hsmallA : level (G.net.tail a) < level (G.net.tail b) := by
          apply lt_of_le_of_ne (hleft a List.mem_concat_self)
          intro heq
          have ha0 := hI2 a (by simpa only [hba] using heq)
          omega
        have hsmallB : level (G.net.head b) < level (G.net.tail b) := by
          cases B with
          | nil =>
            have heb : e = b := by simpa using congrArg List.getLast? htwo
            rw [← heb, hend]
            exact hbad
          | cons c C =>
            have hc : G.net.tail c = G.net.head b := hB.1
            simpa only [hc] using hright c List.mem_cons_self
        have hnegA : G.neg a = false := by
          cases he : G.neg a with
          | false => rfl
          | true =>
            have hzero := (hI4 a he).2
            rw [← hba] at hzero
            omega
        have hnegB : G.neg b = false := by
          cases he : G.neg b with
          | false => rfl
          | true =>
            have hzero := (hI4 b he).1
            omega
        have ha : G.aux a = false := (huab a (by simp)).resolve_right (by simp [hnegA])
        have hb : G.aux b = false := (huab b (by simp)).resolve_right (by simp [hnegB])
        obtain ⟨Q, hQpath, hQuse, hQhop, hQweight, hQlevels⟩ :=
          hI3 a b ha hb hba.symm (by simpa only [hba] using hpeak)
            (by simpa only [hba] using hsmallA) (by simpa only [hba] using hsmallB)
        have hQpos : 0 < G.hops Q := by simp [hQhop]
        obtain ⟨f, hfQ, hflag⟩ := List.countP_pos_iff.mp hQpos
        obtain ⟨C, D, hQsplit, _⟩ := List.eq_append_cons_of_mem hfQ
        have hQp : G.net.IsPathFrom (G.net.tail a) (G.net.head b) (C ++ f :: D) := hQsplit ▸ hQpath
        obtain ⟨hC, hD⟩ := (path_append_cons_iff G.net).mp hQp
        let keptPrefix := A ++ C
        let newSuffix := (f :: D) ++ B
        have hprefix : G.net.IsPathFrom r (G.net.tail f) keptPrefix :=
          (path_append_iff G.net A C).mpr ⟨G.net.tail a, hA, hC⟩
        have hsuffix : G.net.IsPathFrom (G.net.tail f) u newSuffix :=
          (path_append_iff G.net (f :: D) B).mpr ⟨G.net.head b, ⟨rfl, hD⟩, hB⟩
        have hnew : keptPrefix ++ newSuffix = A ++ (Q ++ B) := by
          simp only [keptPrefix, newSuffix, hQsplit, List.append_assoc]
        have hnewUse : ∀ x ∈ keptPrefix ++ newSuffix, G.Usable x := by
          intro x hx
          rw [hnew] at hx
          simp only [List.mem_append] at hx
          rcases hx with hAx | hQx | hBx
          · exact huab x (List.mem_append_left _ hAx)
          · exact hQuse x hQx
          · exact huab x (by simp [hBx])
        have hbound : ∀ x ∈ newSuffix, level (G.net.tail x) ≤ level (G.net.tail b) - 1 := by
          intro x hx
          have hxlt : level (G.net.tail x) < level (G.net.tail b) := by
            rcases List.mem_append.mp hx with hDx | hBx
            · have hQx : x ∈ Q := hQsplit.symm ▸ List.mem_append_right C hDx
              simpa only [hba] using (hQlevels x hQx).1
            · exact hright x hBx
          omega
        have hk' : level (G.net.tail b) - 1 < k := by omega
        obtain ⟨P', e', hP', hU', hH', hW', hpos', hzero'⟩ :=
          ih _ hk' (G.net.tail f) u newSuffix (hI4 f hflag).1 (by simp [newSuffix]) hsuffix
            (fun x hx => hnewUse x (List.mem_append_right keptPrefix hx)) hbound
        have hnewHops : G.hops (keptPrefix ++ newSuffix) = G.hops (P ++ [e]) + 1 := by
          rw [hnew, htwo]
          simp only [hops_append, hQhop]
          simp only [WGraph.hops, List.countP_cons, hnegA, hnegB, Bool.false_eq_true, if_false]
          omega
        have hnewWeight : pathWeight G.w (keptPrefix ++ newSuffix) = pathWeight G.w (P ++ [e]) := by
          rw [hnew, htwo]
          simp only [pathWeight_append, pathWeight_cons, hQweight]
          ring
        refine ⟨keptPrefix ++ P', e', ?_, ?_, ?_, ?_, hpos', hzero'⟩
        · rw [List.append_assoc]
          exact (path_append_iff G.net keptPrefix (P' ++ [e'])).mpr ⟨G.net.tail f, hprefix, hP'⟩
        · rw [List.append_assoc]
          intro x hx
          rcases List.mem_append.mp hx with hpre | hsuf
          · exact hnewUse x (List.mem_append_left _ hpre)
          · exact hU' x hsuf
        · rw [List.append_assoc, hops_append]
          rw [hops_append] at hnewHops
          omega
        · rw [List.append_assoc, pathWeight_append, hW', ← pathWeight_append]
          exact hnewWeight

/-- The forward Unfolding Lemma with an arbitrary level-zero starting vertex. -/
theorem unfold_forward {V E : Type} (G : WGraph V E) (level : V → ℕ) (t : ℕ)
    (hlev : ∀ v, level v ≤ t) (hI2 : G.I2 level) (hI3 : G.I3Path level) (hI4 : G.I4 level)
    (r u : V) (h : ℕ) (P₀ : List E) (e : E) (hr : level r = 0)
    (hp : G.net.IsPathFrom r u (P₀ ++ [e])) (hu : ∀ x ∈ P₀ ++ [e], G.Usable x)
    (hh : G.hops (P₀ ++ [e]) ≤ h) :
    ∃ (P₁ : List E) (e' : E), G.net.IsPathFrom r u (P₁ ++ [e']) ∧
      (∀ x ∈ P₁ ++ [e'], G.Usable x) ∧ G.hops (P₁ ++ [e']) ≤ h + t ∧
      pathWeight G.w (P₁ ++ [e']) = pathWeight G.w (P₀ ++ [e]) ∧
      (0 < level u → level (G.net.tail e') < level u) ∧
      (level u = 0 → level (G.net.tail e') = 0) := by
  obtain ⟨P₁, e', hp', hu', hh', hw', hpos, hzero⟩ :=
    unfold_from_zero G level hI2 hI3 hI4 t r u (P₀ ++ [e]) hr (by simp) hp hu fun x _ => hlev _
  exact ⟨P₁, e', hp', hu', hh'.trans (Nat.add_le_add_right hh _), hw', hpos, hzero⟩

end BFAlmostLinear

namespace BFAlmostLinear.WGraph

open AtomicDynRouting.ResidenceTime

/-- Reverse every incidence, keeping the same arc IDs, flags, and weights. -/
def reversed {V E : Type} (G : WGraph V E) : WGraph V E :=
  { G with net := ⟨G.net.head, G.net.tail⟩ }

private theorem path_append_one {V E : Type} (G : Network V E) {u v : V}
    {P : List E} (hp : G.IsPathFrom u v P) (e : E) (he : G.tail e = v) :
    G.IsPathFrom u (G.head e) (P ++ [e]) := by
  induction P generalizing u with
  | nil => change u = v at hp; exact ⟨he.trans hp.symm, rfl⟩
  | cons f P ih => exact ⟨hp.1, ih hp.2⟩

theorem reversed_path {V E : Type} (G : WGraph V E) {u v : V} {P : List E}
    (hp : G.net.IsPathFrom u v P) : G.reversed.net.IsPathFrom v u P.reverse := by
  induction P generalizing u with
  | nil => exact (show u = v from hp).symm
  | cons e P ih =>
    obtain ⟨rfl, hp⟩ := hp
    rw [List.reverse_cons]
    change G.reversed.net.IsPathFrom v (G.reversed.net.head e) (P.reverse ++ [e])
    exact path_append_one G.reversed.net (ih hp) e rfl

theorem reversed_hops {V E : Type} (G : WGraph V E) (P : List E) :
    G.reversed.hops P.reverse = G.hops P := by simp [hops, reversed]

theorem reversed_weight {V E : Type} (G : WGraph V E) (P : List E) :
    pathWeight G.reversed.w P.reverse = pathWeight G.w P := by
  simp [pathWeight, reversed, List.map_reverse]

theorem reversed_I2 {V E : Type} (G : WGraph V E) (level : V → ℕ)
    (h : G.I2 level) : G.reversed.I2 level := by
  intro e he
  exact he.trans (h e he.symm)

theorem reversed_I4 {V E : Type} (G : WGraph V E) (level : V → ℕ)
    (h : G.I4 level) : G.reversed.I4 level := by
  intro e he
  exact (h e he).symm

theorem reversed_I3Path {V E : Type} (G : WGraph V E) (level : V → ℕ)
    (h : G.I3Path level) : G.reversed.I3Path level := by
  intro a b ha hb hab hpos hin hout
  change G.net.tail a = G.net.head b at hab
  obtain ⟨P,hp,hus,hh,hw,hl⟩ := h b a hb ha hab.symm (hab ▸ hpos)
    (hab ▸ hout) (hab ▸ hin)
  refine ⟨P.reverse, G.reversed_path hp, ?_, (G.reversed_hops P).trans hh, ?_, ?_⟩
  · intro e he
    exact hus e (List.mem_reverse.mp he)
  · rw [reversed_weight, hw, add_comm]
    rfl
  · intro e he
    obtain ⟨h₁,h₂⟩ := hl e (List.mem_reverse.mp he)
    exact ⟨h₂.trans_le (Nat.le_of_eq (congrArg level hab.symm)),
           h₁.trans_le (Nat.le_of_eq (congrArg level hab.symm))⟩

end BFAlmostLinear.WGraph

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime

theorem unfold_backward {V E : Type} (G : WGraph V E) (level : V → ℕ) (t : ℕ)
    (hlev : ∀ v, level v ≤ t) (hI2 : G.I2 level) (hI3 : G.I3Path level) (hI4 : G.I4 level)
    (r u : V) (h : ℕ) (P₀ : List E) (e : E) (hr : level r = 0)
    (hp : G.net.IsPathFrom u r (e :: P₀)) (hu : ∀ x ∈ e :: P₀, G.Usable x)
    (hh : G.hops (e :: P₀) ≤ h) :
    ∃ (P₁ : List E) (e' : E), G.net.IsPathFrom u r (e' :: P₁) ∧
      (∀ x ∈ e' :: P₁, G.Usable x) ∧ G.hops (e' :: P₁) ≤ h + t ∧
      pathWeight G.w (e' :: P₁) = pathWeight G.w (e :: P₀) ∧
      (0 < level u → level (G.net.head e') < level u) ∧
      (level u = 0 → level (G.net.head e') = 0) := by
  have hpR := G.reversed_path hp
  have hhopR := (G.reversed_hops (e :: P₀)).trans_le hh
  have husR (x : E) (hx : x ∈ (e :: P₀).reverse) : G.reversed.Usable x := hu x (List.mem_reverse.mp hx)
  simp only [List.reverse_cons] at hpR hhopR husR
  obtain ⟨Q, f, hQ, huQ, hhQ, hwQ, hlQ⟩ := unfold_forward G.reversed level t hlev
    (G.reversed_I2 level hI2) (G.reversed_I3Path level hI3) (G.reversed_I4 level hI4)
    r u h P₀.reverse e hr hpR husR hhopR
  have hback := G.reversed.reversed_path hQ
  have hhback := (G.reversed.reversed_hops (Q ++ [f])).trans_le hhQ
  have hwback := (G.reversed.reversed_weight (Q ++ [f])).trans hwQ
  have hworig := G.reversed_weight (e :: P₀)
  rw [List.reverse_cons] at hworig
  refine ⟨Q.reverse, f, ?_, ?_, ?_, ?_, hlQ⟩
  · simpa [WGraph.reversed] using hback
  · intro x hx
    apply huQ x
    simpa [or_comm] using hx
  · simpa [WGraph.reversed] using hhback
  · simpa [WGraph.reversed] using hwback.trans hworig

end BFAlmostLinear

open BFAlmostLinear in
/-- **Lemma 4.16 (Unfolding Lemma)**, p.28. "• Suppose that there is an h-hop path P in G(t) from r ∈ N to u and let (w, u) be the
last edge in P. Then there exists an (h + t)-hop path P′ in G(t) from r to u of the same weight as P such that the final edge
(w′, u) in P′ satisfies i(w′) < i(u) if i(u) > 0 and i(w′) = 0 if i(u) = 0. • Suppose that there is an h-hop path P in G(t) from u to
r ∈ N and let (u, w) be the first edge in P. Then there exists an (h + t)-hop path P′ in G(t) from u to r of the same weight as P
such that the first edge (u, w′) in P′ satisfies i(w′) < i(u) if i(u) > 0 and i(w′) = 0 if i(u) = 0."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 4.16, p.28.

**Formalization Note.** The statement is free of the run: any graph with a level function `i` with values at most `t`, (I2), (I4) and
the weight-and-path part of (I3), which is the part preserved by reweighting, so it holds in `G(t)` (p.12: "after applying the
reweighting but before applying the data structure"). `P` is nonempty. `P` and `P′` use real arcs and flagged auxiliary arcs
(`Usable`); with no auxiliary arcs this is every arc. An unflagged auxiliary arc such as (S6) falls outside (I3), so it cannot be
unfolded and is excluded. -/
theorem solution {V E : Type} (G : WGraph V E) (level : V → ℕ) (t : ℕ)
    (hlev : ∀ v, level v ≤ t) (hI2 : G.I2 level) (hI3 : G.I3Path level) (hI4 : G.I4 level) :
    (∀ (r u : V) (h : ℕ) (P₀ : List E) (e : E), G.IsNegVertex r →
      G.net.IsPathFrom r u (P₀ ++ [e]) → (∀ x ∈ P₀ ++ [e], G.Usable x) → G.hops (P₀ ++ [e]) ≤ h →
      ∃ (P₁ : List E) (e' : E), G.net.IsPathFrom r u (P₁ ++ [e']) ∧
        (∀ x ∈ P₁ ++ [e'], G.Usable x) ∧ G.hops (P₁ ++ [e']) ≤ h + t ∧
        pathWeight G.w (P₁ ++ [e']) = pathWeight G.w (P₀ ++ [e]) ∧
        (0 < level u → level (G.net.tail e') < level u) ∧
        (level u = 0 → level (G.net.tail e') = 0)) ∧
    (∀ (r u : V) (h : ℕ) (P₀ : List E) (e : E), G.IsNegVertex r →
      G.net.IsPathFrom u r (e :: P₀) → (∀ x ∈ e :: P₀, G.Usable x) → G.hops (e :: P₀) ≤ h →
      ∃ (P₁ : List E) (e' : E), G.net.IsPathFrom u r (e' :: P₁) ∧
        (∀ x ∈ e' :: P₁, G.Usable x) ∧ G.hops (e' :: P₁) ≤ h + t ∧
        pathWeight G.w (e' :: P₁) = pathWeight G.w (e :: P₀) ∧
        (0 < level u → level (G.net.head e') < level u) ∧
        (level u = 0 → level (G.net.head e') = 0)) := by
  constructor
  · intro r u h P₀ e hneg hp hu hh
    obtain ⟨a, htail, hflag, _⟩ := hneg
    have hr : level r = 0 := htail ▸ (hI4 a hflag).1
    exact unfold_forward G level t hlev hI2 hI3 hI4 r u h P₀ e hr hp hu hh
  · intro r u h P₀ e hneg hp hu hh
    obtain ⟨a, htail, hflag, _⟩ := hneg
    have hr : level r = 0 := htail ▸ (hI4 a hflag).1
    exact unfold_backward G level t hlev hI2 hI3 hI4 r u h P₀ e hr hp hu hh
