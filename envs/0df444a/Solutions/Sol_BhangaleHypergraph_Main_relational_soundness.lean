-- Prove2me | solution 1 for BhangaleHypergraph.Main.relational_soundness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T08:10:20.097817+00:00
-- url     : https://prove2.me/submissions/27a6fbbb-ff9e-449e-ae4a-b81247b75e7d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BhangaleHypergraph_Main_simultaneous_selectors
import Definitions.Def_BhangaleHypergraph_Main_Relational

open BhangaleHypergraph.Main
open scoped Classical

set_option maxHeartbeats 1600000

private lemma mem_closed {G : Layered} {C s : ℕ} {x : Fin G.n}
    {A : Finset (Fin (G.R x))} :
    A ∈ Closed G C s x ↔ ∃ (y : Fin G.n) (p : DirectedPath G x y)
      (B : Finset (Fin (G.R y))), B ∈ Core C s (G.R y) ∧
        A = Preimage p.projection B := by
  simp [Closed]

private noncomputable def localCore (G : Layered) (C : ℕ)
    (col : RelVertex G C → Fin C)
    (hcol : ∀ u v w, (Relational G C).triple u v w →
      ¬ (col u = col v ∧ col v = col w)) (x : Fin G.n) : CoreColoring C where
  R := G.R x
  positive := G.positive x
  W := Closed G C (C ^ (C - 1)) x
  core_subset := by
    intro A hA
    rw [mem_closed]
    refine ⟨x, DirectedPath.nil x, A, hA, ?_⟩
    change A = Preimage (id : Fin (G.R x) → Fin (G.R x)) A
    simp [Preimage]
  color := fun A => col (Quot.mk _ ⟨x, A⟩)
  admissible := by
    intro A B D hNAE heq
    apply hcol (Quot.mk _ ⟨x, A⟩) (Quot.mk _ ⟨x, B⟩) (Quot.mk _ ⟨x, D⟩)
    · exact ⟨x, A, B, D, hNAE, rfl, rfl, rfl⟩
    · exact heq

private lemma local_exact_minor (G : Layered) (C : ℕ)
    (col : RelVertex G C → Fin C)
    (hcol : ∀ u v w, (Relational G C).triple u v w →
      ¬ (col u = col v ∧ col v = col w)) (e : Fin G.edges) :
    ExactMinor (localCore G C col hcol (G.src e)).color
      (localCore G C col hcol (G.dst e)).color (G.proj e) := by
  intro B
  have hclosed : Preimage (G.proj e) B.val ∈ Closed G C (C ^ (C - 1)) (G.src e) := by
    rcases mem_closed.mp B.property with ⟨z, p, A, hA, hBA⟩
    rw [mem_closed]
    refine ⟨z, DirectedPath.cons e p, A, hA, ?_⟩
    rw [hBA]
    apply Finset.ext
    intro a
    simp only [Preimage, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  refine ⟨hclosed, ?_⟩
  change col (Quot.mk _ ⟨G.dst e, B⟩) =
    col (Quot.mk _ ⟨G.src e, ⟨Preimage (G.proj e) B.val, hclosed⟩⟩)
  apply congrArg col
  symm
  apply Quot.sound
  exact ⟨e, B.val, B.property, hclosed, rfl, rfl⟩

private def StrictPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

private def strictPairFinset (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)

private lemma mem_strictPairFinset (n : ℕ) (p : Fin n × Fin n) :
    p ∈ strictPairFinset n ↔ p.1 < p.2 := by
  simp only [strictPairFinset, Finset.mem_filter, Finset.mem_univ, true_and]

private instance (n : ℕ) : Fintype (StrictPair n) :=
  Fintype.ofFinset (strictPairFinset n) (fun p => by
    rw [mem_strictPairFinset]
    exact Iff.rfl)

private lemma card_strictPair (n : ℕ) :
    Fintype.card (StrictPair n) = Nat.choose n 2 := by
  let P := (Finset.univ : Finset (Fin n)).powersetCard 2
  have hcard : Fintype.card (StrictPair n) = P.card := by
    change Fintype.card {p : Fin n × Fin n // p.1 < p.2} = P.card
    rw [Fintype.card_subtype]
    change (strictPairFinset n).card = P.card
    apply Finset.card_bij (fun p _ => ({p.1, p.2} : Finset (Fin n)))
    · intro p hp
      rw [mem_strictPairFinset] at hp
      simp [P, Finset.card_pair (ne_of_lt hp)]
    · intro p hp q hq heq
      rw [mem_strictPairFinset] at hp hq
      have hp1 : p.1 = q.1 ∨ p.1 = q.2 := by
        have hm : p.1 ∈ ({q.1, q.2} : Finset (Fin n)) := by
          rw [← heq]
          simp
        simpa using hm
      have hp2 : p.2 = q.1 ∨ p.2 = q.2 := by
        have hm : p.2 ∈ ({q.1, q.2} : Finset (Fin n)) := by
          rw [← heq]
          simp
        simpa using hm
      rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
      · exact False.elim ((ne_of_lt hp) (h1.trans h2.symm))
      · exact Prod.ext h1 h2
      · exfalso
        have hlt : q.2 < q.1 := by simpa [h1, h2] using hp
        exact (not_lt_of_ge (le_of_lt hq) hlt)
      · exact False.elim ((ne_of_lt hp) (h1.trans h2.symm))
    · intro b hb
      have hb2 : b.card = 2 := by simpa [P] using hb
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hb2
      rcases lt_or_gt_of_ne hxy with h | h
      · exact ⟨(x, y), mem_strictPairFinset n _ |>.mpr h, rfl⟩
      · exact ⟨(y, x), mem_strictPairFinset n _ |>.mpr h, Finset.pair_comm y x⟩
  rw [hcard]
  simp [P]

private lemma chain_collision {G : Outer} {C : ℕ} (hlayers : G.layers = C + 1)
    (typ : Fin G.n → Fin C) (c : Chain G.toLayered) :
    ∃ p : StrictPair G.layers, typ (c.vertex p.1.1) = typ (c.vertex p.1.2) := by
  let v : Fin (C + 1) → Fin C := fun a => typ (c.vertex (Fin.cast hlayers.symm a))
  obtain ⟨a, b, hab, hv⟩ := Fintype.exists_ne_map_eq_of_card_lt v (by simp)
  rcases lt_or_gt_of_ne hab with h | h
  · let p : StrictPair G.layers :=
      ⟨((Fin.cast hlayers.symm a), (Fin.cast hlayers.symm b)), h⟩
    exact ⟨p, hv⟩
  · let p : StrictPair G.layers :=
      ⟨((Fin.cast hlayers.symm b), (Fin.cast hlayers.symm a)), h⟩
    exact ⟨p, hv.symm⟩

private lemma choose_pair_and_large_mass (G : Outer) (C : ℕ) (typ : Fin G.n → Fin C)
    (hcoll : ∀ c : Chain G.toLayered, ∃ p : StrictPair G.layers,
      typ (c.vertex p.1.1) = typ (c.vertex p.1.2)) :
    ∃ (choosePair : Chain G.toLayered → StrictPair G.layers),
      (∀ c : Chain G.toLayered, typ (c.vertex (choosePair c).1.1) =
        typ (c.vertex (choosePair c).1.2)) ∧
      ∃ p : StrictPair G.layers, 1 / (Nat.choose G.layers 2 : ℝ) ≤
          ∑ c : Chain G.toLayered, if choosePair c = p then G.mass c else 0 := by
  let choosePair : Chain G.toLayered → StrictPair G.layers :=
    fun c => Classical.choose (hcoll c)
  have hchoose (c : Chain G.toLayered) :
      typ (c.vertex (choosePair c).1.1) = typ (c.vertex (choosePair c).1.2) := by
    exact Classical.choose_spec (hcoll c)
  refine ⟨choosePair, hchoose, ?_⟩
  have hpart : (∑ p : StrictPair G.layers, ∑ c : Chain G.toLayered,
      if choosePair c = p then G.mass c else 0) = ∑ c, G.mass c := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_eq_single (choosePair c)]
    · simp
    · intro q _ hq
      simp [Ne.symm hq]
    · simp
  by_contra hn
  push_neg at hn
  have hne : (Finset.univ : Finset (StrictPair G.layers)).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hpart
    rw [G.total] at hpart
    norm_num at hpart
  have hlt := Finset.sum_lt_sum_of_nonempty hne (fun p _ => hn p)
  rw [hpart, G.total, Finset.sum_const, nsmul_eq_mul] at hlt
  rw [Finset.card_univ, card_strictPair] at hlt
  have hc : 0 < (Nat.choose G.layers 2 : ℝ) := by
    have hcNat : 0 < Nat.choose G.layers 2 := by
      rw [← card_strictPair]
      obtain ⟨q, _⟩ := hne
      exact Fintype.card_pos_iff.mpr ⟨q⟩
    exact_mod_cast hcNat
  have hone : (Nat.choose G.layers 2 : ℝ) *
      (1 / (Nat.choose G.layers 2 : ℝ)) = 1 := by
    field_simp
  rw [hone] at hlt
  exact lt_irrefl 1 hlt

private lemma fixed_two_card_lower {α : Type} [Fintype α] [DecidableEq α]
    {β : α → Type} [∀ x, Fintype (β x)] {u v : α} (huv : u ≠ v)
    (a : β u) (b : β v) :
    (∏ x, Fintype.card (β x)) ≤
      Fintype.card (β u) * Fintype.card (β v) *
        Fintype.card {ρ : (∀ x, β x) // ρ u = a ∧ ρ v = b} := by
  let hv : v ≠ u := Ne.symm huv
  let E0 := Equiv.piSplitAt u β
  let E1 := Equiv.piSplitAt (⟨v, hv⟩ : {x // x ≠ u}) (fun x => β x.1)
  let E := E0.trans ((Equiv.refl (β u)).prodCongr E1)
  let R := (x : {x : {x // x ≠ u} // x ≠ ⟨v, hv⟩}) → β x.1.1
  let emb : R → {ρ : (∀ x, β x) // ρ u = a ∧ ρ v = b} := fun r =>
    ⟨E.symm (a, b, r), by simp [E, E0, E1, hv]⟩
  have hinj : Function.Injective emb := by
    intro r s hrs
    have h := congrArg (fun z => (E z.1).2.2) hrs
    simpa [emb] using h
  have hle : Fintype.card R ≤
      Fintype.card {ρ : (∀ x, β x) // ρ u = a ∧ ρ v = b} :=
    Fintype.card_le_of_injective emb hinj
  have htot : (∏ x, Fintype.card (β x)) =
      Fintype.card (β u) * (Fintype.card (β v) * Fintype.card R) := by
    rw [← Fintype.card_pi]
    rw [Fintype.card_congr E]
    simp [R]
  rw [htot]
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ hle

private lemma fintype_card_irrel (α : Type) (i j : Fintype α) :
    @Fintype.card α i = @Fintype.card α j := by
  rw [← @Nat.card_eq_fintype_card α i, ← @Nat.card_eq_fintype_card α j]

theorem solution (G : Outer) (C : ℕ) (hC : 2 ≤ C)
    (hlayers : G.layers = C + 1) (ε : ℝ) (hsound : PairwiseSound G ε)
    (hε : ε < 1 / ((Nat.choose (C + 1) 2 : ℝ) * ((2 * C : ℕ) : ℝ) ^ (2 * C))) :
    ¬ RelColorable (Relational G.toLayered C) C := by
  rintro ⟨col, hcol⟩
  let core : Fin G.n → CoreColoring C := localCore G.toLayered C col hcol
  obtain ⟨τ, Sel, hSel, hcompat⟩ := simultaneous_selectors C hC
  have hne (x : Fin G.n) : (Sel (core x)).Nonempty := (hSel (core x)).1
  let typ : Fin G.n → Fin C := fun x => τ (core x)
  have hc (c : Chain G.toLayered) : ∃ p : StrictPair G.layers,
      typ (c.vertex p.1.1) = typ (c.vertex p.1.2) := chain_collision hlayers typ c
  obtain ⟨choosePair, hchoose, p, hp⟩ := choose_pair_and_large_mass G C typ hc
  let i : Fin G.layers := p.1.1
  let j : Fin G.layers := p.1.2
  let hij : i < j := p.2
  let d : ℕ := (2 * C) ^ C
  have hd : 0 < d := by dsimp [d]; positivity
  have hselcard (x : Fin G.n) : (Sel (core x)).card ≤ d := (hSel (core x)).2
  have hselpos (x : Fin G.n) : 0 < (Sel (core x)).card := Finset.card_pos.mpr (hne x)
  have hpair (c : Chain G.toLayered) (hc : choosePair c = p) :
      ∃ (a : Fin (G.R (G.src (c.edge i j hij))))
        (b : Fin (G.R (G.dst (c.edge i j hij)))),
        a ∈ Sel (core (G.src (c.edge i j hij))) ∧
        b ∈ Sel (core (G.dst (c.edge i j hij))) ∧
          G.proj (c.edge i j hij) a = b := by
    let e := c.edge i j hij
    have hm := local_exact_minor G.toLayered C col hcol e
    have hm' : ExactMinor (core (G.src e)).color (core (G.dst e)).color (G.proj e) := hm
    have ht : τ (core (G.src e)) = τ (core (G.dst e)) := by
      rw [c.source i j hij, c.target i j hij]
      have hh := hchoose c
      rw [hc] at hh
      exact hh
    have hn := hcompat (core (G.src e)) (core (G.dst e)) (G.proj e) hm' ht
    obtain ⟨b, hb⟩ := hn
    rw [Finset.mem_inter] at hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb.1
    exact ⟨a, b, ha, hb.2, hab⟩
  let Rand := (x : Fin G.n) → Sel (core x)
  let labeling : Rand → Labeling G.toLayered := fun r x => (r x).val
  let good : Chain G.toLayered → Rand → Prop := fun c r =>
    G.proj (c.edge i j hij) ((labeling r) (G.src (c.edge i j hij))) =
      (labeling r) (G.dst (c.edge i j hij))
  let goodCard (c : Chain G.toLayered) : ℕ := Fintype.card {r : Rand // good c r}
  have hfixed (c : Chain G.toLayered) (hc : choosePair c = p) :
      (∏ x, (Sel (core x)).card) ≤ d * d * goodCard c := by
    let e := c.edge i j hij
    obtain ⟨a, b, ha, hb, hab⟩ := hpair c hc
    have huv : G.src e ≠ G.dst e := by
      intro heq
      have hlayer := congrArg G.layer heq
      exact (ne_of_lt (G.forward e)) hlayer
    let a' : Sel (core (G.src e)) := ⟨a, ha⟩
    let b' : Sel (core (G.dst e)) := ⟨b, hb⟩
    have hprod := fixed_two_card_lower (α := Fin G.n) (β := fun x => Sel (core x)) huv a' b'
    simp only [Fintype.card_coe] at hprod
    have hinj : Function.Injective
        (fun (r : {r : Rand // r (G.src e) = a' ∧ r (G.dst e) = b'}) =>
          (⟨r.1, by
            change G.proj e ((labeling r.1) (G.src e)) = (labeling r.1) (G.dst e)
            have h1 : (r.1 (G.src e)).val = a := by rw [r.2.1]
            have h2 : (r.1 (G.dst e)).val = b := by rw [r.2.2]
            simpa [labeling, h1, h2] using hab⟩ : {r : Rand // good c r})) := by
      intro r s hrs
      apply Subtype.ext
      exact congrArg (fun z : Subtype (good c) => z.1) hrs
    have hcards : Fintype.card {r : Rand // r (G.src e) = a' ∧ r (G.dst e) = b'} ≤
        goodCard c := Fintype.card_le_of_injective _ hinj
    have hdd : (Sel (core (G.src e))).card * (Sel (core (G.dst e))).card ≤ d * d :=
      Nat.mul_le_mul (hselcard _) (hselcard _)
    calc
      (∏ x, (Sel (core x)).card) ≤
          (Sel (core (G.src e))).card * (Sel (core (G.dst e))).card *
            Fintype.card {r : Rand // r (G.src e) = a' ∧ r (G.dst e) = b'} := by
              convert hprod using 1
              congr 1
              exact fintype_card_irrel _ _ _
      _ ≤ d * d * goodCard c := Nat.mul_le_mul hdd hcards
  have hRandcard : (Fintype.card Rand : ℝ) = ∏ x, ((Sel (core x)).card : ℝ) := by simp [Rand]
  have hTpos : 0 < (∏ x, ((Sel (core x)).card : ℝ)) := by
    apply Finset.prod_pos
    intro x _
    exact_mod_cast hselpos x
  have hgoodratio (c : Chain G.toLayered) (hc : choosePair c = p) :
      1 / (d : ℝ) ^ 2 ≤ (goodCard c : ℝ) / (∏ x, ((Sel (core x)).card : ℝ)) := by
    have hf := hfixed c hc
    have hf' : (∏ x, ((Sel (core x)).card : ℝ)) ≤ (d : ℝ) ^ 2 * (goodCard c : ℝ) := by
      exact_mod_cast (by simpa [pow_two] using hf :
        (∏ x, (Sel (core x)).card) ≤ d ^ 2 * goodCard c)
    rw [div_le_div_iff₀ (by positivity : 0 < (d : ℝ) ^ 2) hTpos]
    simpa [mul_comm] using hf'
  let success : Rand → ℝ := fun r => ∑ c : Chain G.toLayered,
    if good c r then G.mass c else 0
  have hsum : (∑ r : Rand, success r) = ∑ c : Chain G.toLayered,
      G.mass c * (goodCard c : ℝ) := by
    simp only [success]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    have hi : (∑ r : Rand, if good c r then G.mass c else 0) =
        G.mass c * (goodCard c : ℝ) := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      rw [show (Finset.univ.filter fun r : Rand => good c r).card = goodCard c by
        exact (Fintype.card_subtype (good c)).symm]
      ring
    rw [hi]
  have hAvg : 1 / ((Nat.choose G.layers 2 : ℝ) * (d : ℝ) ^ 2) ≤
      (∑ r : Rand, success r) / (∏ x, ((Sel (core x)).card : ℝ)) := by
    rw [hsum]
    have hfinite : (∑ c : Chain G.toLayered,
        if choosePair c = p then G.mass c / (d : ℝ) ^ 2 else 0) ≤
        ∑ c : Chain G.toLayered,
          G.mass c * ((goodCard c : ℝ) / (∏ x, ((Sel (core x)).card : ℝ))) := by
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : choosePair c = p
      · simp only [hc, if_true]
        have hg := hgoodratio c hc
        have := mul_le_mul_of_nonneg_left hg (G.nonneg c)
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
      · simp only [hc, if_false]
        exact mul_nonneg (G.nonneg c) (div_nonneg (Nat.cast_nonneg _) hTpos.le)
    calc
      1 / ((Nat.choose G.layers 2 : ℝ) * (d : ℝ) ^ 2) =
          (1 / (Nat.choose G.layers 2 : ℝ)) / (d : ℝ) ^ 2 := by ring
      _ ≤ (∑ c : Chain G.toLayered, if choosePair c = p then G.mass c else 0) /
          (d : ℝ) ^ 2 := by gcongr
      _ = ∑ c : Chain G.toLayered,
          if choosePair c = p then G.mass c / (d : ℝ) ^ 2 else 0 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro c _
            by_cases hc : choosePair c = p
            · rw [if_pos hc, if_pos hc]
            · simp only [if_neg hc, zero_div]
      _ ≤ ∑ c : Chain G.toLayered,
          G.mass c * ((goodCard c : ℝ) / (∏ x, ((Sel (core x)).card : ℝ))) := hfinite
      _ = (∑ c : Chain G.toLayered, G.mass c * (goodCard c : ℝ)) /
          (∏ x, ((Sel (core x)).card : ℝ)) := by
            simp_rw [← mul_div_assoc]
            rw [Finset.sum_div]
  have hRand : (Finset.univ : Finset Rand).Nonempty := by
    let r : Rand := fun x => ⟨(hne x).choose, (hne x).choose_spec⟩
    exact ⟨r, Finset.mem_univ r⟩
  obtain ⟨r, hr⟩ : ∃ r : Rand,
      1 / ((Nat.choose G.layers 2 : ℝ) * (d : ℝ) ^ 2) ≤ success r := by
    by_contra hn
    push_neg at hn
    have hlt := Finset.sum_lt_sum_of_nonempty hRand (fun r _ => hn r)
    have hcard : (Fintype.card Rand : ℝ) = ∏ x, ((Sel (core x)).card : ℝ) := hRandcard
    have hlt' : (∑ r : Rand, success r) <
        (∏ x, ((Sel (core x)).card : ℝ)) *
          (1 / ((Nat.choose G.layers 2 : ℝ) * (d : ℝ) ^ 2)) := by simpa [hcard, mul_comm] using hlt
    have hdiv : (∑ r : Rand, success r) / (∏ x, ((Sel (core x)).card : ℝ)) <
        1 / ((Nat.choose G.layers 2 : ℝ) * (d : ℝ) ^ 2) :=
          (div_lt_iff₀ hTpos).mpr (by simpa [mul_comm] using hlt')
    exact (not_lt_of_ge hAvg) hdiv
  have hpv := hsound (labeling r) i j hij
  have hval : PairValue G (labeling r) i j hij = success r := by
    simp only [PairValue, success, good, mul_ite, mul_one, mul_zero]
  rw [hval] at hpv
  have hpow : (d : ℝ) ^ 2 = ((2 * C : ℕ) : ℝ) ^ (2 * C) := by
    dsimp [d]
    push_cast
    rw [← pow_mul, Nat.mul_comm C 2]
  have hlow : 1 / ((Nat.choose (C + 1) 2 : ℝ) * ((2 * C : ℕ) : ℝ) ^ (2 * C)) ≤
      success r := by simpa only [hlayers, hpow] using hr
  exact (not_lt_of_ge (hlow.trans hpv)) hε
