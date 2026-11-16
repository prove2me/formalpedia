-- Prove2me | solution 1 for DirKECC1549.Main.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-15T14:19:36.079019+00:00
-- url     : https://prove2.me/submissions/469d2d0c-57f2-4f63-a487-713f24466ce4

import Mathlib
import Definitions.Def_DirKECC1549_Main_Alg3
import Theorems.Thm_DirKECC1549_Main_edge_menger_cut
import Theorems.Thm_DirKECC1549_Main_edge_menger_avoid
import Theorems.Thm_DirKECC1549_Main_trail_family_flow
import Theorems.Thm_DirKECC1549_Main_unit_flow_cut_bound
import Theorems.Thm_DirKECC1549_Main_sec2_maxflow_mincut
import Theorems.Thm_DirKECC1549_Main_claim_1

set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Main.Lemma4Aux

open DirKECC1549.Main

variable {n m : ℕ}

/-- Weak duality: `k` edge-disjoint `x → y` paths cross every `(x, y)`-cut in `k` distinct edges. -/
theorem paths_le_cut (D : Fin m → Fin n × Fin n) (k : ℕ) (x y : Fin n)
    (h : HasDisjointPaths D k x y) (S : Finset (Fin n)) (hx : x ∈ S) (hy : y ∉ S) :
    k ≤ outCount D S := by
  obtain ⟨P, hP, hd⟩ := h
  exact unit_flow_cut_bound D x y k _ (trail_family_flow D x y k P hP hd) S ⟨hx, hy⟩

/-- `k`-edge-connectivity is the absence of a separating set with fewer than `k` leaving edges. -/
theorem kec_iff_not_sep (k : ℕ) (D : Fin m → Fin n × Fin n) (u v : Fin n) :
    KEdgeConnected k D u v ↔
      ¬ ∃ S : Finset (Fin n), ((u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)) ∧ outCount D S < k := by
  constructor
  · rintro (rfl | ⟨huv, hvu⟩) ⟨S, hS, hlt⟩
    · rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h2 h1
    · rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (paths_le_cut D k u v huv S h1 h2) (not_le.2 hlt)
      · exact absurd (paths_le_cut D k v u hvu S h1 h2) (not_le.2 hlt)
  · intro h
    by_cases huv : u = v
    · exact Or.inl huv
    refine Or.inr ⟨edge_menger_cut D k u v huv ?_, edge_menger_cut D k v u (Ne.symm huv) ?_⟩
    · intro S hu hv
      by_contra hlt
      exact h ⟨S, Or.inl ⟨hu, hv⟩, not_le.1 hlt⟩
    · intro S hv hu
      by_contra hlt
      exact h ⟨S, Or.inr ⟨hv, hu⟩, not_le.1 hlt⟩

/-- Edges leaving `S` in the reverse graph are the edges leaving `Sᶜ` in the graph. -/
theorem outCount_rev (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) :
    outCount (Rev D) S = outCount D Sᶜ := by
  unfold outCount outEdges Rev
  congr 1
  ext e
  simp [and_comm]

/-- `k`-edge-connectivity is the same in `D` and in its reverse. -/
theorem kec_rev (k : ℕ) (D : Fin m → Fin n × Fin n) (u v : Fin n) :
    KEdgeConnected k (Rev D) u v ↔ KEdgeConnected k D u v := by
  rw [kec_iff_not_sep, kec_iff_not_sep]
  apply not_congr
  constructor
  · rintro ⟨S, hS, hlt⟩
    refine ⟨Sᶜ, ?_, by rwa [← outCount_rev]⟩
    simp only [mem_compl]
    tauto
  · rintro ⟨S, hS, hlt⟩
    refine ⟨Sᶜ, ?_, by rwa [outCount_rev, compl_compl]⟩
    simp only [mem_compl]
    tauto

/-- `k`-edge-connectivity for `k = 1` is strong connectivity. -/
theorem paths_one_iff_reach (D : Fin m → Fin n × Fin n) (x y : Fin n) :
    HasDisjointPaths D 1 x y ↔ Reach D x y := by
  rw [edge_menger_avoid]
  constructor
  · intro h
    obtain ⟨p, hp, -⟩ := h ∅ (by simp)
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩ F hF
    have : F = ∅ := Finset.card_eq_zero.1 (by omega)
    subst this
    exact ⟨p, hp, by simp⟩

/-- `outCount` as a sum of indicators over all edges. -/
theorem outCount_eq_sum (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) :
    (outCount D S : ℤ) = ∑ e : Fin m, if (D e).1 ∈ S ∧ (D e).2 ∉ S then 1 else 0 := by
  unfold outCount outEdges
  rw [Finset.card_filter]
  push_cast
  rfl

/-- Summing the flow-conservation equation over `S`: the net number of flow edges leaving `S`. -/
theorem flow_net_out (D : Fin m → Fin n × Fin n) (F : Finset (Fin m)) (z r : Fin n) (q : ℕ)
    (hF : IsUnitFlow D F z r q) (S : Finset (Fin n)) :
    (∑ e : Fin m, if e ∈ F then
        ((if (D e).1 ∈ S then (1 : ℤ) else 0) - (if (D e).2 ∈ S then 1 else 0)) else 0) =
      (if z ∈ S then (q : ℤ) else 0) - (if r ∈ S then (q : ℤ) else 0) := by
  have h1 : ∀ x : Fin n, ((F.filter (fun e => (D e).1 = x)).card : ℤ) =
      ∑ e : Fin m, if e ∈ F then (if (D e).1 = x then (1 : ℤ) else 0) else 0 := by
    intro x
    rw [Finset.card_filter]
    push_cast
    rw [← Finset.sum_filter]
    simp
  have h2 : ∀ x : Fin n, ((F.filter (fun e => (D e).2 = x)).card : ℤ) =
      ∑ e : Fin m, if e ∈ F then (if (D e).2 = x then (1 : ℤ) else 0) else 0 := by
    intro x
    rw [Finset.card_filter]
    push_cast
    rw [← Finset.sum_filter]
    simp
  calc (∑ e : Fin m, if e ∈ F then
          ((if (D e).1 ∈ S then (1 : ℤ) else 0) - (if (D e).2 ∈ S then 1 else 0)) else 0)
      = ∑ e : Fin m, ∑ x ∈ S,
          ((if e ∈ F then (if (D e).1 = x then (1 : ℤ) else 0) else 0) -
            (if e ∈ F then (if (D e).2 = x then (1 : ℤ) else 0) else 0)) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_sub_distrib]
        by_cases he : e ∈ F
        · simp only [he, if_true]
          rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
        · simp [he]
    _ = ∑ x ∈ S, ∑ e : Fin m,
          ((if e ∈ F then (if (D e).1 = x then (1 : ℤ) else 0) else 0) -
            (if e ∈ F then (if (D e).2 = x then (1 : ℤ) else 0) else 0)) := Finset.sum_comm
    _ = ∑ x ∈ S, (((F.filter (fun e => (D e).1 = x)).card : ℤ) -
          (F.filter (fun e => (D e).2 = x)).card) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [h1, h2, Finset.sum_sub_distrib]
    _ = ∑ x ∈ S, ((if x = z then (q : ℤ) else 0) - (if x = r then (q : ℤ) else 0)) :=
        Finset.sum_congr rfl (fun x _ => hF x)
    _ = (if z ∈ S then (q : ℤ) else 0) - (if r ∈ S then (q : ℤ) else 0) := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

/-- The cut identity for the residual graph of a unit flow:
`out_H(S) = out_D(S) − q·[z ∈ S] + q·[r ∈ S]`. -/
theorem flip_outCount (D : Fin m → Fin n × Fin n) (F : Finset (Fin m)) (z r : Fin n) (q : ℕ)
    (hF : IsUnitFlow D F z r q) (S : Finset (Fin n)) :
    (outCount (flipEdges D F) S : ℤ) =
      outCount D S - (if z ∈ S then (q : ℤ) else 0) + (if r ∈ S then (q : ℤ) else 0) := by
  have hnet := flow_net_out D F z r q hF S
  rw [outCount_eq_sum, outCount_eq_sum, sub_add, ← hnet, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  unfold flipEdges
  by_cases he : e ∈ F <;> by_cases ha : (D e).1 ∈ S <;> by_cases hb : (D e).2 ∈ S <;>
    simp [he, ha, hb]

/-- `λ_D(z, r)` is at most the size of any `(z, r)`-cut. -/
theorem lam_le_cut (D : Fin m → Fin n × Fin n) (z r : Fin n) (hzr : z ≠ r)
    (S : Finset (Fin n)) (hz : z ∈ S) (hr : r ∉ S) : lam D z r ≤ outCount D S :=
  (sec2_maxflow_mincut D z r hzr).2.2 ⟨S, ⟨hz, hr⟩, rfl⟩

/-- The large-cut step of Lemma 4. Let `S` separate `u` and `v`, avoid the root `r`, have fewer
than `k` leaving edges and out-volume above `Δ`. A Lemma 2 hitting set `Z` contains some `z ∈ S`;
then `q = λ_D(z, r) < k`, and in the residual graph `H` of a value-`q` flow, `S` has
`out_H(S) = out_D(S) − q < k − q` leaving edges, so `u, v` are not `(k − q)`-edge-connected in `H`.
Hence the refinement by the recursive run on `(H, k − q)` separates `u` and `v`. -/
theorem large_case (D : Fin m → Fin n × Fin n) (r : Fin n) (k Δ : ℕ)
    (Z : Finset (Fin n)) (q : Fin n → ℕ) (F : Fin n → Finset (Fin m))
    (Q : Fin n → Fin n → Fin n → Prop)
    (hL2 : Lemma2Guarantee D r k Δ Z)
    (hq : ∀ z ∈ Z, q z = min k (lam D z r) ∧ IsUnitFlow D (F z) z r (q z))
    (ih : ∀ z ∈ Z, q z < k → 1 ≤ k - q z →
      ∀ a b, Q z a b ↔ KEdgeConnected (k - q z) (flipEdges D (F z)) a b)
    (u v : Fin n) (hQ : ∀ z ∈ Z, q z < k → Q z u v)
    (S : Finset (Fin n)) (hsep : (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)) (hrS : r ∉ S)
    (hout : outCount D S < k) (hvol : Δ < vol D S) : False := by
  obtain ⟨z, hzS, hzZ⟩ := Finset.nonempty_iff_ne_empty.2
    (Finset.nonempty_iff_ne_empty.1 (hL2.2.2 S hrS hout hvol)) |>.imp fun _ h => Finset.mem_inter.1 h
  have hzr : z ≠ r := fun h => hL2.1 (h ▸ hzZ)
  obtain ⟨hqz, hflow⟩ := hq z hzZ
  have hlam := lam_le_cut D z r hzr S hzS hrS
  have hqk : q z < k := by rw [hqz]; omega
  have hqS : q z ≤ outCount D S := by rw [hqz]; omega
  have hkec := (ih z hzZ hqk (by omega) u v).1 (hQ z hzZ hqk)
  have hflip := flip_outCount D (F z) z r (q z) hflow S
  simp only [hzS, hrS, if_true, if_false] at hflip
  rw [kec_iff_not_sep] at hkec
  exact hkec ⟨S, hsep, by omega⟩

/-- The small-cut step: a `(< k)`-out set of `D ∈ {G, Gᴿ}` of out-volume at most `Δ` that
separates `u` and `v` shows that `u, v` are not `(k, Δ)`-connected. -/
theorem not_kdelta (G : Fin m → Fin n × Fin n) (k Δ : ℕ) (D : Fin m → Fin n × Fin n)
    (hD : D = G ∨ D = Rev G) (u v : Fin n) (S : Finset (Fin n))
    (hsep : (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)) (hout : outCount D S < k) (hvol : vol D S ≤ Δ) :
    ¬ KDeltaConnected k Δ G u v := by
  intro h
  have hD' : D ∈ ({G, Rev G} : Set (Fin m → Fin n × Fin n)) := by
    rcases hD with rfl | rfl <;> simp
  have hlt : IsLtOut D k S := by
    refine ⟨?_, ?_, hout⟩
    · rcases hsep with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact ⟨_, h1⟩
    · rintro rfl
      rcases hsep with ⟨-, h2⟩ | ⟨-, h2⟩ <;> exact h2 (Finset.mem_univ _)
  exact h D hD' S hlt hvol hsep

end DirKECC1549.Main.Lemma4Aux

open DirKECC1549.Main DirKECC1549.Main.Lemma4Aux

theorem solution {n m : ℕ} (G : Fin m → Fin n × Fin n) (k : ℕ) (hk : 1 ≤ k)
    (P : Fin n → Fin n → Prop) (hrun : Alg3Run n m G k P) :
    ∀ u v, P u v ↔ KEdgeConnected k G u v := by
  revert hk
  induction hrun with
  | base G k hb =>
    intro hk u v
    rcases hb with rfl | hn
    · constructor
      · intro h
        by_cases huv : u = v
        · exact Or.inl huv
        · exact Or.inr ⟨(paths_one_iff_reach G u v).2 h.1, (paths_one_iff_reach G v u).2 h.2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨⟨[], IsWalk.nil u⟩, ⟨[], IsWalk.nil u⟩⟩
        · exact ⟨(paths_one_iff_reach G u v).1 h1, (paths_one_iff_reach G v u).1 h2⟩
    · have huv : u = v := Fin.ext (by have := u.isLt; have := v.isLt; omega)
      subst huv
      exact ⟨fun _ => Or.inl rfl, fun _ => ⟨⟨[], IsWalk.nil u⟩, ⟨[], IsWalk.nil u⟩⟩⟩
  | split G k runs hb hsc hruns ih =>
    intro hk u v
    rw [claim_1 k hk G u v]
    constructor
    · rintro ⟨hu, hv, h⟩
      exact ⟨(Finset.mem_filter.1 hv).2, hu, hv, (ih u hk _ _).1 h⟩
    · rintro ⟨-, hu, hv, h⟩
      exact ⟨hu, hv, (ih u hk _ _).2 h⟩
  | @main n' m' G k Pk1 P r ZG ZR qG qR FG FR QG QR hb hsc hPk1 hL1 hL2G hL2R hqG hQG hqR hQR
      ihPk1 ihQG ihQR =>
    intro hk u v
    have hk2 : 2 ≤ k := by omega
    constructor
    · rintro ⟨hP, hG, hR⟩
      have hkm1 : KEdgeConnected (k - 1) G u v := (ihPk1 (by omega) u v).1 (hL1.2.1 u v hP)
      rw [kec_iff_not_sep]
      rintro ⟨S, hsep, hout⟩
      by_cases hvol : vol G S ≤ alg3Delta n' m' k
      · exact hL1.2.2.2 u v hkm1 (not_kdelta G k _ G (Or.inl rfl) u v S hsep hout hvol) hP
      replace hvol := not_le.1 hvol
      by_cases hrS : r ∈ S
      · -- pass to the complement in the reverse graph
        have hsep' : (u ∈ Sᶜ ∧ v ∉ Sᶜ) ∨ (v ∈ Sᶜ ∧ u ∉ Sᶜ) := by
          simp only [Finset.mem_compl]; tauto
        have hout' : outCount (Rev G) Sᶜ < k := by rwa [outCount_rev, compl_compl]
        by_cases hvol' : vol (Rev G) Sᶜ ≤ alg3Delta n' m' k
        · exact hL1.2.2.2 u v hkm1
            (not_kdelta G k _ (Rev G) (Or.inr rfl) u v Sᶜ hsep' hout' hvol') hP
        replace hvol' := not_le.1 hvol'
        exact large_case (Rev G) r k _ ZR qR FR QR hL2R hqR ihQR u v hR Sᶜ hsep'
          (by simpa using hrS) hout' hvol'
      · exact large_case G r k _ ZG qG FG QG hL2G hqG ihQG u v hG S hsep hrS hout hvol
    · intro hkec
      refine ⟨hL1.2.2.1 u v hkec, ?_, ?_⟩
      · intro z hz hq
        refine (ihQG z hz hq (by omega) u v).2 ?_
        rw [kec_iff_not_sep] at hkec ⊢
        rintro ⟨S, hsep, hout⟩
        have hflip := flip_outCount G (FG z) z r (qG z) (hqG z hz).2 S
        apply hkec ⟨S, hsep, ?_⟩
        split_ifs at hflip <;> omega
      · intro z hz hq
        refine (ihQR z hz hq (by omega) u v).2 ?_
        rw [← kec_rev] at hkec
        rw [kec_iff_not_sep] at hkec ⊢
        rintro ⟨S, hsep, hout⟩
        have hflip := flip_outCount (Rev G) (FR z) z r (qR z) (hqR z hz).2 S
        apply hkec ⟨S, hsep, ?_⟩
        split_ifs at hflip <;> omega
