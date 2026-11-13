-- Prove2me | solution 1 for FatFlat.Hereditary.theorem_1_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:11:53.247399+00:00
-- url     : https://prove2.me/submissions/785e4ba3-f39c-4836-a9e0-5f320502b416

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes
import Theorems.Thm_FatFlat_Hereditary_lemma_4_2

section
set_option autoImplicit false

namespace FatFlat.Dev.L42
open FatFlat.Hereditary

section Dist
variable {V : Type} {G : SimpleGraph V}

lemma hom_edist_le {V' : Type} {G' : SimpleGraph V'} (f : G →g G') (u v : V) :
    G'.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.edist u v = ⊤
  · simp [h]
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    calc G'.edist (f u) (f v) ≤ (p.map f).length := SimpleGraph.edist_le _
      _ = G.edist u v := by rw [SimpleGraph.Walk.length_map, hp]

lemma edist_le_induce (S : Set V) (a b : ↥S) :
    G.edist (a : V) (b : V) ≤ (G.induce S).edist a b :=
  hom_edist_le (SimpleGraph.Embedding.induce S).toHom a b

end Dist

section Radius
variable {V : Type} {G : SimpleGraph V}

lemma radius_mono {S : Set V} {r r' : ℕ} (h : RadiusLE G S r) (hr : r ≤ r') : RadiusLE G S r' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun v => (hc v).trans (by exact_mod_cast hr)⟩

lemma radius_connected {S : Set V} {r : ℕ} (h : RadiusLE G S r) : (G.induce S).Connected := by
  obtain ⟨c, hc⟩ := h
  have hr : ∀ v, (G.induce S).Reachable c v := fun v =>
    SimpleGraph.reachable_of_edist_ne_top
      (ne_top_of_le_ne_top (ENat.natCast_ne_top r) (hc v))
  have : Nonempty ↥S := ⟨c⟩
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

lemma radius_image {V' : Type} {G' : SimpleGraph V'} (F : G' ↪g G) {S : Set V'} {r : ℕ}
    (h : RadiusLE G' S r) : RadiusLE G (F '' S) r := by
  obtain ⟨c, hc⟩ := h
  let φ : G'.induce S →g G.induce (F '' S) :=
    ⟨fun x => ⟨F x, ⟨x, x.2, rfl⟩⟩, by
      intro x y hxy
      simpa using F.map_adj_iff.mpr hxy⟩
  refine ⟨φ c, fun v' => ?_⟩
  obtain ⟨y, hy, hyv⟩ := v'.2
  have : v' = φ ⟨y, hy⟩ := Subtype.ext hyv.symm
  rw [this]
  exact (hom_edist_le φ c ⟨y, hy⟩).trans (hc _)

end Radius

section OneSub
variable {W : Type}

end OneSub

section Model
variable {W V : Type}

lemma transfer {V' : Type} (H : SimpleGraph W) {G' : SimpleGraph V'} {G : SimpleGraph V}
    (F : G' ↪g G) (a b : ℕ) (h : IsShallowInducedMinorOneSubdiv H G' a b) :
    IsShallowInducedMinorOneSubdiv H G a b := by
  obtain ⟨M, hA, hB⟩ := h
  have hR : ∀ w, ∃ r, RadiusLE G' (M.B w) r := by
    rintro (u | x)
    · exact ⟨a, hA u⟩
    · exact ⟨b, hB x⟩
  refine ⟨⟨fun w => F '' (M.B w), fun w => (M.nonempty w).image F, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u w huw
    exact (Set.disjoint_image_iff F.injective).mpr (M.disjoint huw)
  · intro w
    obtain ⟨r, hr⟩ := hR w
    exact radius_connected (radius_image F hr)
  · intro u w huw
    rw [← M.adj_iff u w huw]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hadj⟩
      exact ⟨x, hx, y, hy, F.map_adj_iff.mp hadj⟩
    · rintro ⟨x, hx, y, hy, hadj⟩
      exact ⟨F x, ⟨x, hx, rfl⟩, F y, ⟨y, hy, rfl⟩, F.map_adj_iff.mpr hadj⟩
  · exact fun u => radius_image F (hA u)
  · exact fun x => radius_image F (hB x)

lemma mono_radius (H : SimpleGraph W) (G : SimpleGraph V) {a a' b b' : ℕ}
    (h : IsShallowInducedMinorOneSubdiv H G a b) (ha : a ≤ a') (hb : b ≤ b') :
    IsShallowInducedMinorOneSubdiv H G a' b' := by
  obtain ⟨M, hA, hB⟩ := h
  exact ⟨M, fun u => radius_mono (hA u) ha, fun x => radius_mono (hB x) hb⟩

end Model

section Path
variable {V : Type} {G : SimpleGraph V}

end Path

end FatFlat.Dev.L42
end

section
set_option autoImplicit false

namespace FatFlat.Dev.T13
open FatFlat.Hereditary FatFlat.Dev.L42

/-! ### The size sequence -/

/-- `σ_h = 4^5 (h+1)^10 + h`. -/
def sigma (h : ℕ) : ℕ := 4 ^ 5 * (h + 1) ^ 10 + h

/-- The sizes of the sets `A_i` needed in the iteration, read backwards from `m`. -/
def aseq (h m : ℕ) : ℕ → ℕ
  | 0 => m
  | (k + 1) => (aseq h m k + sigma h) ^ (10 ^ h) + m

lemma aseq_ge (h m k : ℕ) : m ≤ aseq h m k := by
  cases k with
  | zero => exact le_rfl
  | succ k => simp only [aseq]; omega

lemma aseq_le (h m Z : ℕ) (hq : 2 ≤ 10 ^ h) (hZσ : sigma h ≤ Z) (hZm : m ≤ Z)
    (hZq : 2 ^ (10 ^ h) + 1 ≤ Z) :
    ∀ k, aseq h m k ≤ Z ^ (2 * (10 ^ h) ^ k - 1) := by
  intro k
  induction k with
  | zero => simpa [aseq] using hZm
  | succ k ih =>
    set q := 10 ^ h with hqdef
    have hZ1 : 1 ≤ Z := by
      have : 1 ≤ 2 ^ q := Nat.one_le_two_pow
      omega
    have hqk : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
    set e := 2 * q ^ k - 1 with he
    have h1 : Z ≤ Z ^ e := Nat.le_self_pow (by omega) Z
    have h2 : aseq h m k + sigma h ≤ 2 * Z ^ e := by omega
    have h3 : (aseq h m k + sigma h) ^ q ≤ (2 * Z ^ e) ^ q := Nat.pow_le_pow_left h2 q
    have h4 : (2 * Z ^ e) ^ q = 2 ^ q * Z ^ (e * q) := by rw [mul_pow, ← pow_mul]
    have h5 : m ≤ Z ^ (e * q) := by
      calc m ≤ Z := hZm
        _ ≤ Z ^ (e * q) := Nat.le_self_pow (by have : 1 ≤ e := by omega
                                               have : 1 ≤ q := by omega
                                               positivity) Z
    have h6 : aseq h m (k + 1) ≤ (2 ^ q + 1) * Z ^ (e * q) := by
      have hdef : aseq h m (k + 1) = (aseq h m k + sigma h) ^ q + m := rfl
      rw [hdef]
      calc _ ≤ 2 ^ q * Z ^ (e * q) + Z ^ (e * q) := by omega
        _ = _ := by ring
    have h7 : (2 ^ q + 1) * Z ^ (e * q) ≤ Z * Z ^ (e * q) := Nat.mul_le_mul_right _ hZq
    have h8 : Z * Z ^ (e * q) = Z ^ (e * q + 1) := by ring
    have h9 : e * q + 1 ≤ 2 * q ^ (k + 1) - 1 := by
      have hk : e + 1 = 2 * q ^ k := by omega
      have key : e * q + q = 2 * (q ^ k * q) := by
        calc e * q + q = (e + 1) * q := by ring
          _ = 2 * q ^ k * q := by rw [hk]
          _ = _ := by ring
      rw [pow_succ]
      generalize q ^ k * q = y at *
      generalize e * q = w at *
      omega
    calc aseq h m (k + 1) ≤ Z ^ (e * q + 1) := by omega
      _ ≤ Z ^ (2 * q ^ (k + 1) - 1) := Nat.pow_le_pow_right (by omega) h9

/-- the exponent bound `m * a_s ≤ m ^ (2 ^ (30 h d))` for `m ≥ 2`, `s ≤ d` -/
lemma size_bound (h d s m : ℕ) (hh : 0 < h) (hd : 0 < d) (hs : s ≤ d) (hm : 2 ≤ m) :
    m * aseq h m s ≤ m ^ (2 ^ (30 * (h * d))) := by
  set q := 10 ^ h with hq
  have hq2 : 2 ≤ q := by
    calc 2 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  set γ := q + sigma h with hγ
  set Z := m ^ γ with hZ
  have hσ1 : 1 ≤ sigma h := by
    unfold sigma
    have : 1 ≤ 4 ^ 5 * (h + 1) ^ 10 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hγ1 : 1 ≤ γ := by omega
  have h2γ : 2 ^ γ ≤ Z := Nat.pow_le_pow_left hm γ
  have hZσ : sigma h ≤ Z := by
    have : sigma h < 2 ^ sigma h := Nat.lt_two_pow_self
    have : 2 ^ sigma h ≤ 2 ^ γ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hZm : m ≤ Z := Nat.le_self_pow (by omega) m
  have hZq : 2 ^ q + 1 ≤ Z := by
    have : 2 ^ (q + 1) ≤ 2 ^ γ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
    have : 2 ^ q + 1 ≤ 2 ^ (q + 1) := by rw [pow_succ]; omega
    omega
  have hA := aseq_le h m Z hq2 hZσ hZm hZq s
  -- crude bounds on the constants
  have hq16 : q ≤ 2 ^ (4 * h) := by
    calc q = 10 ^ h := rfl
      _ ≤ 16 ^ h := Nat.pow_le_pow_left (by norm_num) h
      _ = 2 ^ (4 * h) := by rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
  have hh2 : h + 1 ≤ 2 ^ h := Nat.lt_two_pow_self
  have hσ : sigma h ≤ 2 ^ (11 + 10 * h) := by
    have h1 : (h + 1) ^ 10 ≤ 2 ^ (10 * h) := by
      calc (h + 1) ^ 10 ≤ (2 ^ h) ^ 10 := Nat.pow_le_pow_left hh2 10
        _ = 2 ^ (10 * h) := by rw [← pow_mul]; ring_nf
    have h2 : 4 ^ 5 * (h + 1) ^ 10 ≤ 2 ^ (10 + 10 * h) := by
      calc 4 ^ 5 * (h + 1) ^ 10 ≤ 2 ^ 10 * 2 ^ (10 * h) := Nat.mul_le_mul (by norm_num) h1
        _ = 2 ^ (10 + 10 * h) := by rw [pow_add]
    have h3 : h ≤ 2 ^ (10 + 10 * h) := by
      calc h ≤ 2 ^ h := by omega
        _ ≤ 2 ^ (10 + 10 * h) := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold sigma
    calc _ ≤ 2 ^ (10 + 10 * h) + 2 ^ (10 + 10 * h) := by omega
      _ = 2 ^ (11 + 10 * h) := by rw [← two_mul, ← pow_succ']; ring_nf
  have hγ2 : γ ≤ 2 ^ (12 + 10 * h) := by
    have : 2 ^ (4 * h) ≤ 2 ^ (11 + 10 * h) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc γ ≤ 2 ^ (11 + 10 * h) + 2 ^ (11 + 10 * h) := by omega
      _ = 2 ^ (12 + 10 * h) := by rw [← two_mul, ← pow_succ']; ring_nf
  have hqs : q ^ s ≤ 2 ^ (4 * (h * d)) := by
    calc q ^ s ≤ (2 ^ (4 * h)) ^ s := Nat.pow_le_pow_left hq16 s
      _ = 2 ^ (4 * h * s) := by rw [← pow_mul]
      _ ≤ 2 ^ (4 * (h * d)) := Nat.pow_le_pow_right (by norm_num) (by
          have : h * s ≤ h * d := Nat.mul_le_mul_left h hs
          nlinarith)
  have hqs1 : 1 ≤ q ^ s := Nat.one_le_pow _ _ (by omega)
  have hexp : 1 + γ * (2 * q ^ s - 1) ≤ 2 ^ (30 * (h * d)) := by
    have h1 : 1 + γ * (2 * q ^ s - 1) ≤ 2 * (γ * q ^ s) := by
      have : γ * (2 * q ^ s - 1) + γ = γ * (2 * q ^ s) := by
        rw [← Nat.mul_succ]; congr 1; omega
      nlinarith
    have h2 : 2 * (γ * q ^ s) ≤ 2 ^ (13 + 10 * h + 4 * (h * d)) := by
      calc 2 * (γ * q ^ s) ≤ 2 * (2 ^ (12 + 10 * h) * 2 ^ (4 * (h * d))) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul hγ2 hqs)
        _ = 2 ^ (13 + 10 * h + 4 * (h * d)) := by
            rw [← pow_add, ← pow_succ']; ring_nf
    have h3 : 13 + 10 * h + 4 * (h * d) ≤ 30 * (h * d) := by
      have h4 : h ≤ h * d := Nat.le_mul_of_pos_right h hd
      have h5 : 1 ≤ h * d := by omega
      generalize h * d = u at *
      omega
    exact h1.trans (h2.trans (Nat.pow_le_pow_right (by norm_num) h3))
  calc m * aseq h m s ≤ m * Z ^ (2 * q ^ s - 1) := Nat.mul_le_mul_left m hA
    _ = m ^ (1 + γ * (2 * q ^ s - 1)) := by rw [hZ, ← pow_mul, pow_add, pow_one]
    _ ≤ m ^ (2 ^ (30 * (h * d))) := Nat.pow_le_pow_right (by omega) hexp

end FatFlat.Dev.T13
end

section
set_option autoImplicit false

namespace FatFlat.Dev.T13
open FatFlat.Hereditary FatFlat.Dev.L42

lemma ball_union {V : Type} (G : SimpleGraph V) (S T : Set V) (r : ℕ) :
    ball G (S ∪ T) r = ball G S r ∪ ball G T r := by
  ext x
  simp only [ball, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz | hz, hd⟩
    · exact Or.inl ⟨z, hz, hd⟩
    · exact Or.inr ⟨z, hz, hd⟩
  · rintro (⟨z, hz, hd⟩ | ⟨z, hz, hd⟩)
    · exact ⟨z, Or.inl hz, hd⟩
    · exact ⟨z, Or.inr hz, hd⟩

lemma so_mono {V : Type} {G : SimpleGraph V} {α α' : ℕ} (hα : α ≤ α') {Z B : Set V}
    (h : IsScatteredOff G α' Z B) : IsScatteredOff G α Z B := fun a b ha hb hab =>
  lt_of_le_of_lt (by exact_mod_cast hα) (h a b ha hb hab)

lemma so_subset {V : Type} {G : SimpleGraph V} {α : ℕ} {Z B B' : Set V} (hB : B' ⊆ B)
    (h : IsScatteredOff G α Z B) : IsScatteredOff G α Z B' := fun a b ha hb hab =>
  h a b (hB ha) (hB hb) hab

lemma oneSubdiv_to_induced {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) (r : ℕ)
    (h : IsShallowInducedMinorOneSubdiv H G r r) : IsShallowInducedMinor (oneSubdivision H) G r := by
  obtain ⟨M, hA, hB⟩ := h
  refine ⟨M, ?_⟩
  rintro (u | x)
  · exact hA u
  · exact hB x

/-- Lemma 4.2 applied in `G - Z`, with the conclusion phrased in `G`. -/
lemma step42 (h d m : ℕ) (hh : 0 < h) (hd : 2 ≤ d) (hm : 0 < m) {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hG : ¬ IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * d) 6)
    (Z : Set V) (A' : Finset V) (hAZ : ∀ a ∈ A', a ∉ Z)
    (hsc : IsScatteredOff G (2 * d) Z (A' : Set V))
    (hcard : (max (4 ^ 5 * (h + 1) ^ 10) (m + h - 1)) ^ (10 ^ h) ≤ A'.card) :
    ∃ X : Finset V, X.card ≤ h ∧ ∃ B : Finset V, B ⊆ A' ∧ m ≤ B.card ∧
      IsScatteredOff G (2 * (d + 1)) (Z ∪ ball G (X : Set V) 37) (B : Set V) := by
  classical
  let A'' : Finset ↥Zᶜ := A'.subtype (fun x => x ∈ Zᶜ)
  have hcardA'' : A''.card = A'.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun a ha => hAZ a ha)
  have hmemA'' : ∀ a : ↥Zᶜ, a ∈ A'' ↔ (a : V) ∈ A' := fun a => by
    simp [A'']
  have hsc'' : IsScattered (G.induce Zᶜ) (2 * d) (A'' : Set ↥Zᶜ) := by
    intro a ha b hb hab
    exact hsc a b ((hmemA'' a).mp ha) ((hmemA'' b).mp hb) hab
  have hG' : ¬ IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) (G.induce Zᶜ) (3 * d) 6 :=
    fun h' => hG (transfer _ (SimpleGraph.Embedding.induce Zᶜ) _ _ h')
  obtain ⟨X'', hX''c, B'', hB''A, hB''c, hB''sc⟩ :=
    FatFlat.Hereditary.lemma_4_2 h d m hh hd hm ↥Zᶜ (G.induce Zᶜ) hG' A'' hsc''
      (by rw [hcardA'']; exact hcard)
  refine ⟨X''.map (Function.Embedding.subtype _), by rw [Finset.card_map]; exact hX''c,
    B''.map (Function.Embedding.subtype _), ?_, by rw [Finset.card_map]; exact hB''c, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (hmemA'' y).mp (hB''A hy)
  · intro a b ha hb hab
    obtain ⟨a', ha', ha'v⟩ := Finset.mem_map.mp (Finset.mem_coe.mp ha)
    obtain ⟨b', hb', hb'v⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hb)
    have haZ : (a : V) ∈ Zᶜ := fun h' => a.2 (Or.inl h')
    have hbZ : (b : V) ∈ Zᶜ := fun h' => b.2 (Or.inl h')
    have ea : a' = ⟨a, haZ⟩ := Subtype.ext ha'v
    have eb : b' = ⟨b, hbZ⟩ := Subtype.ext hb'v
    have hnb : ∀ y : ↥(Z ∪ ball G ((X''.map (Function.Embedding.subtype _) : Finset V) : Set V) 37)ᶜ,
        (⟨y.1, fun h' => y.2 (Or.inl h')⟩ : ↥Zᶜ) ∉ ball (G.induce Zᶜ) (X'' : Set ↥Zᶜ) 37 := by
      rintro y ⟨z, hz, hd'⟩
      apply y.2
      right
      refine ⟨z.1, ?_, (edist_le_induce _ _ z).trans hd'⟩
      simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe]
      exact ⟨z, hz, rfl⟩
    let φ : G.induce (Z ∪ ball G ((X''.map (Function.Embedding.subtype _) : Finset V) : Set V) 37)ᶜ
        →g (G.induce Zᶜ).induce (ball (G.induce Zᶜ) (X'' : Set ↥Zᶜ) 37)ᶜ :=
      ⟨fun y => ⟨⟨y.1, fun h' => y.2 (Or.inl h')⟩, hnb y⟩, fun {y y'} hyy' => hyy'⟩
    subst ea eb
    have h1 := hB''sc ⟨⟨a, haZ⟩, hnb a⟩ ⟨⟨b, hbZ⟩, hnb b⟩ ha' hb'
      (fun hc => by
        have e1 := congrArg Subtype.val hc
        have e2 := congrArg Subtype.val e1
        exact hab (Subtype.ext e2))
    exact lt_of_lt_of_le h1 (hom_edist_le φ a b)

/-- A greedy `37`-scattered subset. -/
lemma greedy {V : Type} (G : SimpleGraph V) (A : Finset V) (m : ℕ)
    (hlt : ∀ v, (A.filter (fun a => G.edist a v ≤ ((37 : ℕ) : ℕ∞))).card < m) :
    ∃ B : Finset V, B ⊆ A ∧ IsScattered G 37 (B : Set V) ∧ A.card ≤ B.card * m := by
  classical
  have hne : (Finset.filter (fun B : Finset V => IsScattered G 37 (B : Set V)) A.powerset).Nonempty :=
    ⟨∅, by simp [IsScattered]⟩
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hB
  obtain ⟨hBA, hBs⟩ := hB
  have hcover : ∀ a ∈ A, ∃ b ∈ B, G.edist a b ≤ ((37 : ℕ) : ℕ∞) := by
    intro a ha
    by_contra hc
    push Not at hc
    have haB : a ∉ B := fun h' => by
      have := hc a h'
      simp at this
    have hins : insert a B ∈ Finset.filter (fun B : Finset V => IsScattered G 37 (B : Set V)) A.powerset := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset ha hBA, ?_⟩
      intro x hx y hy hxy
      rw [Finset.coe_insert, Set.mem_insert_iff] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact hc y hy
      · rw [SimpleGraph.edist_comm]; exact hc x hx
      · exact hBs x hx y hy hxy
    have := hmax _ hins
    rw [Finset.card_insert_of_notMem haB] at this
    omega
  have hsub : A ⊆ B.biUnion (fun b => A.filter (fun a => G.edist a b ≤ ((37 : ℕ) : ℕ∞))) := by
    intro a ha
    obtain ⟨b, hb, hd⟩ := hcover a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hd⟩⟩
  refine ⟨B, hBA, hBs, ?_⟩
  calc A.card ≤ (B.biUnion _).card := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ B, (A.filter (fun a => G.edist a b ≤ ((37 : ℕ) : ℕ∞))).card :=
        Finset.card_biUnion_le
    _ ≤ B.card • m := Finset.sum_le_card_nsmul _ _ _ (fun b _ => (hlt b).le)
    _ = B.card * m := by rw [smul_eq_mul]

end FatFlat.Dev.T13
end

section
set_option autoImplicit false

namespace FatFlat.Dev.T13
open FatFlat.Hereditary FatFlat.Dev.L42

/-- The state after `j` rounds of the iteration. -/
def Stage {V : Type} (G : SimpleGraph V) (A : Finset V) (h m s j : ℕ) (Aj X : Finset V) : Prop :=
  Aj ⊆ A ∧ X.card ≤ h * j ∧ IsScatteredOff G (2 * (18 + j)) (ball G (X : Set V) 37) (Aj : Set V) ∧
    aseq h m (s - j) ≤ Aj.card

/-- The iteration of §4.2 (Theorem 1.3), for `m ≥ 2`. -/
lemma drill (h d m : ℕ) (hh : 0 < h) (hd : 0 < d) (hm : 2 ≤ m) {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hno : ¬ IsShallowInducedMinor (oneSubdivision (⊤ : SimpleGraph (Fin h))) G (3 * d))
    (A : Finset V) (hA : m * aseq h m (d - 18) ≤ A.card) :
    ∃ X : Finset V, X.card ≤ h * d ∧ ∃ B : Finset V, B ⊆ A ∧ m ≤ B.card ∧
      IsScatteredOff G (2 * d) (ball G (X : Set V) 37) (B : Set V) := by
  classical
  generalize hs : d - 18 = s at hA
  have key : ∀ j, j ≤ s → (∃ X : Finset V, X.card ≤ h * d ∧ ∃ B : Finset V, B ⊆ A ∧ m ≤ B.card ∧
      IsScatteredOff G (2 * d) (ball G (X : Set V) 37) (B : Set V)) ∨
      ∃ Aj X : Finset V, Stage G A h m s j Aj X := by
    intro j
    induction j with
    | zero =>
      intro _
      by_cases hv : ∃ v : V, m ≤ (A.filter (fun a => G.edist a v ≤ ((37 : ℕ) : ℕ∞))).card
      · left
        obtain ⟨v, hv⟩ := hv
        refine ⟨{v}, by simp only [Finset.card_singleton]; exact Nat.mul_pos hh hd, _, Finset.filter_subset _ _, hv, ?_⟩
        intro a b ha _ _
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
        exact absurd ⟨v, by simp, this⟩ a.2
      · right
        push Not at hv
        obtain ⟨B, hBA, hBs, hBc⟩ := greedy G A m hv
        refine ⟨B, ∅, hBA, by simp, ?_, ?_⟩
        · intro a b ha hb hab
          have := hBs a ha b hb (fun h' => hab (Subtype.ext h'))
          calc ((2 * (18 + 0) : ℕ) : ℕ∞) < ((37 : ℕ) : ℕ∞) := by norm_num
            _ < G.edist a b := this
            _ ≤ _ := edist_le_induce _ a b
        · have hmpos : 0 < m := by omega
          have : aseq h m s * m ≤ B.card * m := by
            calc aseq h m s * m = m * aseq h m s := by ring
              _ ≤ A.card := hA
              _ ≤ B.card * m := hBc
          simpa using Nat.le_of_mul_le_mul_right this hmpos
    | succ j ih =>
      intro hj
      rcases ih (by omega) with hgoal | ⟨Aj, X, hsub, hXc, hsc, hcard⟩
      · exact Or.inl hgoal
      set Z : Set V := ball G (X : Set V) 37 with hZ
      set Bi : Finset V := Aj.filter (fun a => a ∈ Z) with hBi
      set A' : Finset V := Aj.filter (fun a => a ∉ Z) with hA'
      have hsum : Bi.card + A'.card = Aj.card := Finset.card_filter_add_card_filter_not _
      have hBiZ : ∀ a ∈ Bi, a ∈ Z := fun a ha => (Finset.mem_filter.mp ha).2
      have hA'Z : ∀ a ∈ A', a ∉ Z := fun a ha => (Finset.mem_filter.mp ha).2
      have hA'sub : A' ⊆ Aj := Finset.filter_subset _ _
      have hBisub : Bi ⊆ Aj := Finset.filter_subset _ _
      by_cases hmB : m ≤ Bi.card
      · left
        refine ⟨X, ?_, Bi, hBisub.trans hsub, hmB, ?_⟩
        · calc X.card ≤ h * j := hXc
            _ ≤ h * d := Nat.mul_le_mul_left h (by omega)
        · intro a b ha hb _
          exact absurd (hBiZ _ (Finset.mem_coe.mp ha)) a.2
      right
      obtain ⟨k, hk⟩ : ∃ k, s - j = k + 1 := ⟨s - j - 1, by omega⟩
      have hk' : s - (j + 1) = k := by rw [Nat.sub_add_eq, hk, Nat.add_sub_cancel]
      have hak : m ≤ aseq h m k := aseq_ge h m k
      have hAj : (aseq h m k + sigma h) ^ (10 ^ h) + m ≤ Aj.card := by
        have := hcard
        rw [hk] at this
        exact this
      set m' : ℕ := aseq h m k - Bi.card with hm'
      have hm'pos : 0 < m' := by omega
      have hRmax : max (4 ^ 5 * (h + 1) ^ 10) (m' + h - 1) ≤ aseq h m k + sigma h := by
        unfold sigma
        apply max_le <;> omega
      have hcardA' : (max (4 ^ 5 * (h + 1) ^ 10) (m' + h - 1)) ^ (10 ^ h) ≤ A'.card := by
        calc _ ≤ (aseq h m k + sigma h) ^ (10 ^ h) := Nat.pow_le_pow_left hRmax _
          _ ≤ A'.card := by omega
      have hG : ¬ IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * (18 + j)) 6 := by
        intro hmodel
        apply hno
        apply oneSubdiv_to_induced
        exact mono_radius (⊤ : SimpleGraph (Fin h)) G hmodel (a' := 3 * d) (b' := 3 * d)
          (by clear * - hs hj; omega) (by clear * - hs hj; omega)
      have hsc' : IsScatteredOff G (2 * (18 + j)) Z (A' : Set V) :=
        so_subset (by exact_mod_cast hA'sub) hsc
      obtain ⟨X', hX'c, B', hB'A', hB'c, hB'sc⟩ :=
        step42 h (18 + j) m' hh (by omega) hm'pos G hG Z A' hA'Z hsc' hcardA'
      have hdisj : Disjoint Bi B' := by
        rw [Finset.disjoint_left]
        intro a haB haC
        exact hA'Z a (hB'A' haC) (hBiZ a haB)
      refine ⟨Bi ∪ B', X ∪ X', ?_, ?_, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact hsub (hBisub ha)
        · exact hsub (hA'sub (hB'A' ha))
      · calc (X ∪ X').card ≤ X.card + X'.card := Finset.card_union_le _ _
          _ ≤ h * (j + 1) := by rw [Nat.mul_succ]; omega
      · rw [Finset.coe_union, ball_union]
        intro a b ha hb hab
        have haB : (a : V) ∈ B' := by
          rcases Finset.mem_union.mp (Finset.mem_coe.mp ha) with h1 | h1
          · exact absurd (Or.inl (hBiZ _ h1)) a.2
          · exact h1
        have hbB : (b : V) ∈ B' := by
          rcases Finset.mem_union.mp (Finset.mem_coe.mp hb) with h1 | h1
          · exact absurd (Or.inl (hBiZ _ h1)) b.2
          · exact h1
        have := hB'sc a b haB hbB hab
        calc ((2 * (18 + (j + 1)) : ℕ) : ℕ∞) = ((2 * (18 + j + 1) : ℕ) : ℕ∞) := by
              congr 1
          _ < _ := this
      · rw [hk', Finset.card_union_of_disjoint hdisj]
        omega
  rcases key s le_rfl with hgoal | ⟨Aj, X, hsub, hXc, hsc, hcard⟩
  · exact hgoal
  refine ⟨X, ?_, Aj, hsub, ?_, so_mono (by omega) hsc⟩
  · calc X.card ≤ h * s := hXc
      _ ≤ h * d := Nat.mul_le_mul_left h (by omega)
  · simpa [aseq] using hcard

end FatFlat.Dev.T13

namespace FatFlat.Hereditary
open FatFlat.Dev.T13 in
theorem chk_theorem_1_3 : ∃ c : ℕ, ∀ h d : ℕ, 0 < h → 0 < d → ∃ N : ℕ → ℕ,
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ¬ IsShallowInducedMinor (oneSubdivision (⊤ : SimpleGraph (Fin h))) G (3 * d) →
      IsDrillFlat G (2 * d) 37 N (h * d)) ∧
    ∀ m : ℕ, N m ≤ m ^ (2 ^ (c * (h * d))) := by
  refine ⟨30, fun h d hh hd => ⟨fun m => if m < 2 then m else m * aseq h m (d - 18), ?_, ?_⟩⟩
  · intro V _ G hno m A hA
    by_cases hm0 : m = 0
    · subst hm0
      refine ⟨∅, by simp, by simp, ∅, by simp, ?_⟩
      intro a b ha _ _
      simp at ha
    by_cases hm1 : m = 1
    · subst hm1
      simp only [show (1 : ℕ) < 2 by norm_num, if_true] at hA
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
      refine ⟨{a}, by simpa using ha, by simp, ∅, by simp, ?_⟩
      intro x y hx hy hxy
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
      exact absurd (Subtype.ext (hx.trans hy.symm)) hxy
    have hm2 : 2 ≤ m := by omega
    simp only [show ¬ m < 2 by omega, if_false] at hA
    obtain ⟨X, hXc, B, hBA, hBc, hsc⟩ := drill h d m hh hd hm2 G hno A hA
    obtain ⟨B', hB'B, hB'c⟩ := Finset.exists_subset_card_eq hBc
    exact ⟨B', hB'B.trans hBA, hB'c, X, hXc, so_subset (by exact_mod_cast hB'B) hsc⟩
  · intro m
    by_cases hm : m < 2
    · simp only [hm, if_true]
      interval_cases m
      · simp
      · simp
    · simp only [hm, if_false]
      exact size_bound h d (d - 18) m hh hd (by omega) (by omega)

end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_theorem_1_3 := @FatFlat.Hereditary.chk_theorem_1_3
