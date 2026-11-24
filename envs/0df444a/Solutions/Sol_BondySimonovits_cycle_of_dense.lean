-- Prove2me | solution 1 for BondySimonovits.cycle_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:41.291245+00:00
-- url     : https://prove2.me/submissions/bd305ef4-e020-41a5-bee4-a2ece24b15a4

module
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Theorems.Thm_BondySimonovits_exists_mixed
public import Theorems.Thm_BondySimonovits_cycle_construct
public import Theorems.Thm_BondySimonovits_anc_self
public import Theorems.Thm_BondySimonovits_anc_zero
public import Theorems.Thm_BondySimonovits_dist_ne_of_adj
public import Theorems.Thm_BondySimonovits_exists_greedy_path
public import Theorems.Thm_BondySimonovits_parent_exists


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V) [DecidableRel K.Adj]
namespace BondySimonovits
theorem _root_.solution (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v) (x : V) (k i : ℕ)
    (hk : 2 ≤ k) (hik : i + 1 ≤ k) (Y : Finset V)
    (hYL : ∀ v ∈ Y, K.Reachable x v ∧ (K.dist x v = i ∨ K.dist x v = i + 1))
    (hne : Y.Nonempty) (hdeg : ∀ u ∈ Y, 2 * k ≤ (Y.filter (K.Adj u)).card)
    (hmin : ∀ Y' ⊆ Y, Y'.Nonempty → (∀ u ∈ Y', 2 * k ≤ (Y'.filter (K.Adj u)).card) → Y' = Y) :
    ∃ (v : V) (p : K.Walk v v), p.IsCycle ∧ p.length = 2 * k := by
  classical
  have hYadj : ∀ u ∈ Y, ∀ v ∈ Y, K.Adj u v → K.dist x u ≠ K.dist x v :=
    fun u hu v _ h => dist_ne_of_adj K f hf (hYL u hu).1 h
  have lev_of_nbr : ∀ u ∈ Y, K.dist x u = i + 1 → ∀ v ∈ Y, K.Adj u v → K.dist x v = i := by
    intro u hu hul v hv h
    have := hYadj u hu v hv h
    rcases (hYL v hv).2 with h' | h' <;> omega
  -- a vertex in the upper layer
  have hw0 : ∃ w ∈ Y, K.dist x w = i + 1 := by
    obtain ⟨v, hv⟩ := hne
    rcases (hYL v hv).2 with h | h
    · have hc : 0 < (Y.filter (K.Adj v)).card := by have := hdeg v hv; omega
      obtain ⟨u, hu⟩ := Finset.card_pos.1 hc
      rw [Finset.mem_filter] at hu
      refine ⟨u, hu.1, ?_⟩
      have := hYadj v hv u hu.1 hu.2
      rcases (hYL u hu.1).2 with h' | h' <;> omega
    · exact ⟨v, hv, h⟩
  obtain ⟨w0, hw0Y, hw0l⟩ := hw0
  have h2 : 1 < (Y.filter (K.Adj w0)).card := by have := hdeg w0 hw0Y; omega
  obtain ⟨s1, hs1, s2, hs2, hs12⟩ := Finset.one_lt_card.1 h2
  rw [Finset.mem_filter] at hs1 hs2
  have hs1l := lev_of_nbr w0 hw0Y hw0l s1 hs1.1 hs1.2
  have hs2l := lev_of_nbr w0 hw0Y hw0l s2 hs2.1 hs2.2
  -- the BFS parent map
  have hparex : ∀ v, ∃ w, K.Reachable x v → 0 < K.dist x v →
      K.Adj v w ∧ K.dist x w + 1 = K.dist x v := by
    intro v
    by_cases h : K.Reachable x v ∧ 0 < K.dist x v
    · obtain ⟨w, hw⟩ := parent_exists K h.1 h.2
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨v, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose par hpar using hparex
  -- the deepest common ancestor level of the lower layer part of `Y`
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → Prop, P = fun t => ∀ s ∈ Y, K.dist x s = i → ∀ s' ∈ Y,
    K.dist x s' = i → anc K par x t s = anc K par x t s' := ⟨_, rfl⟩
  have hP0 : P 0 := hPdef ▸ fun s hs _ s' hs' _ => by
    rw [anc_zero hpar (hYL s hs).1, anc_zero hpar (hYL s' hs').1]
  have hanc_i : ∀ s, K.dist x s = i → anc K par x i s = s := by
    intro s hs
    have := anc_self (K := K) (par := par) (x := x) s
    rwa [hs] at this
  have hPi : ¬ P i := by
    intro h
    rw [hPdef] at h
    have := h s1 hs1.1 hs1l s2 hs2.1 hs2l
    rw [hanc_i s1 hs1l, hanc_i s2 hs2l] at this
    exact hs12 this
  obtain ⟨j, hjdef⟩ : ∃ j, j = Nat.findGreatest P i := ⟨_, rfl⟩
  have hPj : P j := hjdef ▸ Nat.findGreatest_spec (P := P) (Nat.zero_le i) hP0
  have hji : j ≤ i := hjdef ▸ Nat.findGreatest_le i
  have hji' : j < i := lt_of_le_of_ne hji (fun h => hPi (h ▸ hPj))
  have hPj1 : ¬ P (j + 1) :=
    Nat.findGreatest_is_greatest (P := P) (n := i) (by omega) (by omega)
  obtain ⟨t0, ht0, ht0l, t1, ht1, ht1l, hdiff⟩ : ∃ s ∈ Y, K.dist x s = i ∧ ∃ s' ∈ Y,
      K.dist x s' = i ∧ anc K par x (j + 1) s ≠ anc K par x (j + 1) s' := by
    by_contra hcon
    apply hPj1
    rw [hPdef]
    intro s hs hsl s' hs' hs'l
    by_contra hne'
    exact hcon ⟨s, hs, hsl, s', hs', hs'l, hne'⟩
  obtain ⟨χ, hχdef⟩ : ∃ χ : V → Prop, χ = fun v => anc K par x (j + 1) v = anc K par x (j + 1) t0 :=
    ⟨_, rfl⟩
  obtain ⟨w, hwY, a, b, ⟨haY, hal⟩, ⟨hbY, hbl⟩, hwa, hwb, hχa, hχb⟩ :=
    exists_mixed K (K.dist x) i (2 * k) Y (fun v hv => (hYL v hv).2) hYadj hmin hdeg χ t0 t1
      ⟨ht0, ht0l⟩ ⟨ht1, ht1l⟩ (by rw [hχdef]) (by rw [hχdef]; exact fun h => hdiff h.symm)
  have hwl : K.dist x w = i + 1 := by
    have := hYadj w hwY a haY hwa
    rcases (hYL w hwY).2 with h | h <;> omega
  -- numerology
  obtain ⟨hh, hhdef⟩ : ∃ hh, hh = i - j := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = 2 * k - 2 * hh := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = ℓ - 1 := ⟨_, rfl⟩
  -- a greedy path of length `m` from `w` avoiding `a` and `b`
  obtain ⟨q, hq0, hqadj, hqY, hqinj⟩ := exists_greedy_path K Y {a, b} (2 * k) hdeg w hwY
    (by simp [K.ne_of_adj hwa, K.ne_of_adj hwb]) m
    (by have := Finset.card_le_two (a := a) (b := b); omega)
  have hqlev : ∀ t ≤ m, K.dist x (q t) = if t % 2 = 0 then i + 1 else i := by
    intro t
    induction t with
    | zero => intro _; simp [hq0, hwl]
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h3 := hYadj _ (hqY t (by omega)).1 _ (hqY (t + 1) ht).1 (hqadj t (by omega))
      rcases (hYL _ (hqY (t + 1) ht).1).2 with h4 | h4 <;> split_ifs at h1 ⊢ <;> omega
  have hzl : K.dist x (q m) = i := by
    have := hqlev m le_rfl
    have hm2 : ¬ (m % 2 = 0) := by omega
    simpa only [hm2, ↓reduceIte] using this
  have hzY : q m ∈ Y := (hqY m le_rfl).1
  -- choose the endpoint `e ∈ {a, b}` of the opposite kind to `q m`
  obtain ⟨e, heY, hel, hwe, hqe, hχe⟩ : ∃ e ∈ Y, K.dist x e = i ∧ K.Adj w e ∧
      (∀ t ≤ m, q t ≠ e) ∧ (χ e ↔ ¬ χ (q m)) := by
    by_cases hz : χ (q m)
    · exact ⟨b, hbY, hbl, hwb, fun t ht heq => (hqY t ht).2 (by simp [heq]), by tauto⟩
    · exact ⟨a, haY, hal, hwa, fun t ht heq => (hqY t ht).2 (by simp [heq]), by tauto⟩
  have hyz : anc K par x j (q m) = anc K par x j e := by
    rw [hPdef] at hPj; exact hPj (q m) hzY hzl e heY hel
  have her := (hYL e heY).1
  have hzr := (hYL (q m) hzY).1
  refine cycle_construct K hpar k i j hk hik hji' e q m (by omega) her hel hzr hzl (hq0 ▸ hwe.symm)
    hqadj ?_ hqinj hqe hyz ?_
  · intro t ht
    rcases (hYL _ (hqY t ht).1).2 with h | h <;> omega
  · intro h
    have : χ e ↔ χ (q m) := by simp only [hχdef, h]
    exact iff_not_self (this.symm.trans hχe)
end BondySimonovits
