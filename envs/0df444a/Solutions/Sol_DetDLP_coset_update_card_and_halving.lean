-- Prove2me | solution 1 for DetDLP.coset_update_card_and_halving
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:23:53.105715+00:00
-- url     : https://prove2.me/submissions/3b8339b2-ac49-4ff2-be02-3c17a42af077

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

open DetDLP

private lemma fold_gcd_props {N : ℕ} (Mlab : ℕ) (g : Fin N → ℤ) (s : Finset (Fin N)) :
    let d := s.fold Nat.gcd Mlab (fun j => (g j).natAbs)
    d ∣ Mlab ∧
    (∀ j ∈ s, (d : ℤ) ∣ g j) ∧
    ∃ (t : Fin N → ℤ) (k : ℤ), (d : ℤ) = ∑ j ∈ s, g j * t j + (Mlab : ℤ) * k := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨dvd_refl Mlab, fun _ h => absurd h (Finset.notMem_empty _), ⟨fun _ => 0, 1, by simp⟩⟩
  | insert j₀ s hj₀ ih =>
    dsimp only at ih ⊢
    obtain ⟨hd_M, hd_s, t, k, hbez⟩ := ih
    rw [Finset.fold_insert hj₀]
    set ds := s.fold Nat.gcd Mlab (fun j => (g j).natAbs)
    set dnew := Nat.gcd (g j₀).natAbs ds
    have hdnew_dvd_ds : dnew ∣ ds := Nat.gcd_dvd_right _ _
    have hdnew_dvd_j0 : dnew ∣ (g j₀).natAbs := Nat.gcd_dvd_left _ _
    have hdnew_M : dnew ∣ Mlab := dvd_trans hdnew_dvd_ds hd_M
    have hdnew_s : ∀ j ∈ insert j₀ s, (dnew : ℤ) ∣ g j := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Int.natCast_dvd.mpr hdnew_dvd_j0
      · exact dvd_trans (Int.natCast_dvd_natCast.mpr hdnew_dvd_ds) (hd_s j hjs)
    -- Bézout combination for dnew = gcd(|g j₀|, ds)
    have hgab : (dnew : ℤ) = ((g j₀).natAbs : ℤ) * Nat.gcdA (g j₀).natAbs ds +
        (ds : ℤ) * Nat.gcdB (g j₀).natAbs ds := Nat.gcd_eq_gcd_ab (g j₀).natAbs ds
    let sgn : ℤ := if 0 ≤ g j₀ then 1 else -1
    have habs_eq : ((g j₀).natAbs : ℤ) = g j₀ * sgn := by
      dsimp only [sgn]
      split_ifs with h
      · rw [mul_one, Int.natAbs_of_nonneg h]
      · push Not at h
        rw [mul_neg_one, Int.ofNat_natAbs_of_nonpos (le_of_lt h)]
    let u : ℤ := sgn * Nat.gcdA (g j₀).natAbs ds
    let v : ℤ := Nat.gcdB (g j₀).natAbs ds
    let t' : Fin N → ℤ := fun j => if j = j₀ then u else t j * v
    refine ⟨hdnew_M, hdnew_s, ⟨t', k * v, ?_⟩⟩
    rw [Finset.sum_insert hj₀]
    have hsum_s : ∑ j ∈ s, g j * t' j = (∑ j ∈ s, g j * t j) * v := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : j ≠ j₀ := fun h => hj₀ (h ▸ hj)
      simp only [t', if_neg hne]
      ring
    rw [hsum_s]
    have hj0_term : g j₀ * t' j₀ = ((g j₀).natAbs : ℤ) * Nat.gcdA (g j₀).natAbs ds := by
      simp only [t', ↓reduceIte, u]
      rw [habs_eq]
      ring
    rw [hj0_term, hgab, hbez]
    dsimp only [v]
    ring

theorem solution :
    ∀ (Mlab N : ℕ) [NeZero Mlab], 2 ≤ Mlab → 1 ≤ N →
      ∀ (x0 : Fin N → ZMod Mlab) (B : Matrix (Fin N) (Fin N) ℤ)
        (a : Fin N → ZMod Mlab) (c0 : ZMod Mlab),
        let A := affineCoset Mlab x0 B
        let A' := {x ∈ A | ∑ i : Fin N, a i * x i = c0}
        A'.Nonempty →
        let gstar : ℕ :=
          Finset.univ.fold Nat.gcd Mlab
            (fun j : Fin N => Int.natAbs (∑ i : Fin N, ((a i).val : ℤ) * B i j))
        Nat.card A' * Mlab = Nat.card A * gstar ∧
        ((∑ i : Fin N, a i * x0 i ≠ c0) → gstar < Mlab ∧ 2 * Nat.card A' ≤ Nat.card A) := by
  intro Mlab N _ hM hN x0 B a c0
  dsimp only
  intro hA'ne
  set A : Set (Fin N → ZMod Mlab) := affineCoset Mlab x0 B
  set A' : Set (Fin N → ZMod Mlab) := {x ∈ A | ∑ i : Fin N, a i * x i = c0}
  let g : Fin N → ℤ := fun j => ∑ i : Fin N, ((a i).val : ℤ) * B i j
  set gstar : ℕ := Finset.univ.fold Nat.gcd Mlab (fun j => (g j).natAbs)
  have hfold := fold_gcd_props Mlab g Finset.univ
  dsimp only at hfold
  obtain ⟨hg_dvd_M, hg_dvd_g, tBez, kBez, hBez⟩ := hfold
  have hM_pos : 0 < Mlab := by omega
  have hg_pos : 0 < gstar := Nat.pos_of_dvd_of_pos hg_dvd_M hM_pos
  -- Additive subgroup L = image of t ↦ (B * t mod Mlab)
  let ψ : (Fin N → ℤ) →+ (Fin N → ZMod Mlab) :=
    { toFun := fun t i => ((Matrix.mulVec B t i : ℤ) : ZMod Mlab)
      map_zero' := by ext i; simp [Matrix.mulVec]
      map_add' := fun t₁ t₂ => by ext i; simp [Matrix.mulVec_add] }
  let L : AddSubgroup (Fin N → ZMod Mlab) := ψ.range
  have hA_iff : ∀ x : Fin N → ZMod Mlab, x ∈ A ↔ ∃ z : L, x = x0 + z.1 := by
    intro x
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨⟨ψ t, ⟨t, rfl⟩⟩, funext fun i => ht i⟩
    · rintro ⟨⟨z, ⟨t, rfl⟩⟩, rfl⟩
      exact ⟨t, fun i => rfl⟩
  have hcardA : Nat.card A = Nat.card L := by
    let eA : L ≃ A :=
      { toFun := fun z => ⟨x0 + z.1, (hA_iff _).mpr ⟨z, rfl⟩⟩
        invFun := fun x => ⟨x.1 - x0, by
          obtain ⟨z, hz⟩ := (hA_iff x.1).mp x.2
          have : x.1 - x0 = z.1 := by rw [hz]; abel
          rw [this]; exact z.2⟩
        left_inv := fun z => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp) }
    exact (Nat.card_congr eA).symm
  -- Linear functional φ : L →+ ZMod Mlab, z ↦ ∑ i, a i * z i
  let φ : L →+ ZMod Mlab :=
    { toFun := fun z => ∑ i : Fin N, a i * z.1 i
      map_zero' := by simp
      map_add' := fun z₁ z₂ => by
        simp only [AddSubgroup.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib] }
  -- Pick witness x1 ∈ A'
  obtain ⟨x1, hx1⟩ := hA'ne
  obtain ⟨hx1A, hx1eq⟩ := hx1
  obtain ⟨z1, hz1_eq⟩ := (hA_iff x1).mp hx1A
  have hA'_iff : ∀ x : Fin N → ZMod Mlab, x ∈ A' ↔ ∃ w : φ.ker, x = x1 + w.1.1 := by
    intro x
    constructor
    · rintro ⟨hxA, hxeq⟩
      obtain ⟨z, rfl⟩ := (hA_iff x).mp hxA
      let w : L := z - z1
      have hwker : w ∈ φ.ker := by
        change ∑ i : Fin N, a i * (z.1 i - z1.1 i) = 0
        have h1 : ∑ i : Fin N, a i * (x0 i + z.1 i) = c0 := hxeq
        have h2 : ∑ i : Fin N, a i * (x0 i + z1.1 i) = c0 := by
          simpa [hz1_eq] using hx1eq
        have hdiff : ∑ i : Fin N, a i * ((x0 i + z.1 i) - (x0 i + z1.1 i)) = 0 := by
          simp_rw [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_self]
        simpa using hdiff
      refine ⟨⟨w, hwker⟩, ?_⟩
      ext i
      simp only [hz1_eq, w, AddSubgroup.coe_sub, Pi.add_apply, Pi.sub_apply]
      abel
    · rintro ⟨⟨w, hwker⟩, rfl⟩
      have hxA : x1 + w.1 ∈ A := by
        rw [hA_iff]
        refine ⟨z1 + w, ?_⟩
        ext i; simp only [hz1_eq, AddSubgroup.coe_add, Pi.add_apply]; abel
      have hxeq : ∑ i : Fin N, a i * (x1 i + w.1 i) = c0 := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        have hfw : ∑ i : Fin N, a i * w.1 i = 0 := hwker
        rw [hx1eq, hfw, add_zero]
      exact ⟨hxA, hxeq⟩
  have hcardA' : Nat.card A' = Nat.card φ.ker := by
    let eA' : φ.ker ≃ A' :=
      { toFun := fun w => ⟨x1 + w.1.1, (hA'_iff _).mpr ⟨w, rfl⟩⟩
        invFun := fun x => ⟨⟨x.1 - x1, by
          obtain ⟨w, hw⟩ := (hA'_iff x.1).mp x.2
          have : x.1 - x1 = w.1.1 := by rw [hw]; abel
          rw [this]; exact w.1.2⟩, by
          obtain ⟨w, hw⟩ := (hA'_iff x.1).mp x.2
          have hxeq : x.1 - x1 = w.1.1 := by rw [hw]; abel
          have hker : ∀ h : x.1 - x1 ∈ L, (⟨x.1 - x1, h⟩ : L) ∈ φ.ker := by
            intro h
            have hsub : (⟨x.1 - x1, h⟩ : L) = w.1 := Subtype.ext hxeq
            rw [hsub]; exact w.2
          exact hker _⟩
        left_inv := fun w => Subtype.ext (Subtype.ext (by simp))
        right_inv := fun x => Subtype.ext (by simp) }
    exact (Nat.card_congr eA').symm
  -- Formula for φ (ψ t)
  have hφψ : ∀ t : Fin N → ℤ,
      φ ⟨ψ t, ⟨t, rfl⟩⟩ = ((∑ j : Fin N, g j * t j : ℤ) : ZMod Mlab) := by
    intro t
    change ∑ i : Fin N, a i * ((Matrix.mulVec B t i : ℤ) : ZMod Mlab) = _
    simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [g]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ZMod.natCast_zmod_val (a i)]
    ring
  -- Characterize φ.range as {z : ZMod Mlab | gstar ∣ z.val}
  have hrange_iff : ∀ z : ZMod Mlab, z ∈ φ.range ↔ gstar ∣ z.val := by
    intro z
    constructor
    · rintro ⟨⟨y, ⟨t, rfl⟩⟩, rfl⟩
      rw [hφψ t]
      set S : ℤ := ∑ j : Fin N, g j * t j
      have hg_dvd_S : (gstar : ℤ) ∣ S :=
        Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (hg_dvd_g j (Finset.mem_univ j)) (t j)
      have hmod : (((S : ZMod Mlab).val : ℤ) : ZMod Mlab) = (S : ZMod Mlab) := by
        rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      have hM_dvd : (Mlab : ℤ) ∣ (((S : ZMod Mlab).val : ℤ) - S) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp
      have hg_dvd_diff : (gstar : ℤ) ∣ (((S : ZMod Mlab).val : ℤ) - S) :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hg_dvd_M) hM_dvd
      have hg_dvd_val : (gstar : ℤ) ∣ ((S : ZMod Mlab).val : ℤ) := by
        have := dvd_add hg_dvd_diff hg_dvd_S
        simpa using this
      exact Int.natCast_dvd_natCast.mp hg_dvd_val
    · rintro ⟨q, hq⟩
      let t : Fin N → ℤ := fun j => tBez j * (q : ℤ)
      refine ⟨⟨ψ t, ⟨t, rfl⟩⟩, ?_⟩
      rw [hφψ t]
      have hsum_eq : ∑ j : Fin N, g j * t j = (z.val : ℤ) - (Mlab : ℤ) * (kBez * (q : ℤ)) := by
        have h1 : ∑ j : Fin N, g j * t j = (∑ j : Fin N, g j * tBez j) * (q : ℤ) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by dsimp only [t]; ring
        rw [h1]
        have hzv : (z.val : ℤ) = (gstar : ℤ) * (q : ℤ) := by exact_mod_cast hq
        rw [hzv, hBez]
        ring
      rw [hsum_eq]
      push_cast
      simp
  -- Cardinality of φ.range is Mlab / gstar
  have hcard_range : Nat.card φ.range = Mlab / gstar := by
    let eR : Fin (Mlab / gstar) ≃ φ.range :=
      { toFun := fun r => ⟨((r.val * gstar : ℕ) : ZMod Mlab), by
          rw [hrange_iff]
          have hlt : r.val * gstar < Mlab := by
            calc r.val * gstar < (Mlab / gstar) * gstar := Nat.mul_lt_mul_of_pos_right r.isLt hg_pos
              _ = Mlab := Nat.div_mul_cancel hg_dvd_M
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
          exact dvd_mul_left gstar r.val⟩
        invFun := fun z => ⟨z.1.val / gstar, by
          have hlt : z.1.val < Mlab := ZMod.val_lt z.1
          have hmul : (z.1.val / gstar) * gstar = z.1.val :=
            Nat.div_mul_cancel ((hrange_iff z.1).mp z.2)
          have hmul_M : (Mlab / gstar) * gstar = Mlab := Nat.div_mul_cancel hg_dvd_M
          by_contra hge
          push Not at hge
          have : Mlab ≤ z.1.val := by
            calc Mlab = (Mlab / gstar) * gstar := hmul_M.symm
              _ ≤ (z.1.val / gstar) * gstar := Nat.mul_le_mul_right gstar hge
              _ = z.1.val := hmul
          omega⟩
        left_inv := fun r => Fin.ext (by
          dsimp only
          have hlt : r.val * gstar < Mlab := by
            calc r.val * gstar < (Mlab / gstar) * gstar := Nat.mul_lt_mul_of_pos_right r.isLt hg_pos
              _ = Mlab := Nat.div_mul_cancel hg_dvd_M
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel _ hg_pos])
        right_inv := fun z => Subtype.ext (by
          dsimp only
          rw [Nat.div_mul_cancel ((hrange_iff z.1).mp z.2), ZMod.natCast_zmod_val]) }
    rw [← Nat.card_congr eR, Nat.card_fin]
  -- First Isomorphism Theorem: Nat.card φ.ker * Nat.card φ.range = Nat.card L
  have hlagrange : Nat.card φ.ker * Nat.card φ.range = Nat.card L := by
    have hq : Nat.card (L ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
    rw [← hq, ← AddSubgroup.index_eq_card, AddSubgroup.card_mul_index]
  have hcard_rel : Nat.card A' * Mlab = Nat.card A * gstar := by
    rw [hcardA', hcardA]
    calc Nat.card φ.ker * Mlab
        = Nat.card φ.ker * ((Mlab / gstar) * gstar) := by rw [Nat.div_mul_cancel hg_dvd_M]
      _ = (Nat.card φ.ker * Nat.card φ.range) * gstar := by rw [hcard_range, mul_assoc]
      _ = Nat.card L * gstar := by rw [hlagrange]
  refine ⟨hcard_rel, fun hviol => ?_⟩
  -- Halving on violation
  have hφz1_ne : φ z1 ≠ 0 := by
    intro h0
    apply hviol
    have h1 : ∑ i : Fin N, a i * (x0 i + z1.1 i) = c0 := by simpa [hz1_eq] using hx1eq
    simp_rw [mul_add, Finset.sum_add_distrib] at h1
    have h2 : ∑ i : Fin N, a i * z1.1 i = 0 := h0
    rw [h2, add_zero] at h1
    exact h1
  have hval_pos : 0 < (φ z1).val := by
    by_contra h0
    have hv0 : (φ z1).val = 0 := by omega
    exact hφz1_ne ((ZMod.val_eq_zero _).mp hv0)
  have hval_lt : (φ z1).val < Mlab := ZMod.val_lt _
  have hg_dvd_z1 : gstar ∣ (φ z1).val := (hrange_iff (φ z1)).mp ⟨z1, rfl⟩
  have hg_lt : gstar < Mlab := lt_of_le_of_lt (Nat.le_of_dvd hval_pos hg_dvd_z1) hval_lt
  have h2g_le : 2 * gstar ≤ Mlab := by
    obtain ⟨q, hq⟩ := hg_dvd_M
    have hq2 : 2 ≤ q := by
      by_contra hlt2
      have hq01 : q = 0 ∨ q = 1 := by omega
      rcases hq01 with rfl | rfl <;> omega
    calc 2 * gstar = gstar * 2 := by ring
      _ ≤ gstar * q := Nat.mul_le_mul_left gstar hq2
      _ = Mlab := hq.symm
  have h2A'_le : 2 * Nat.card A' ≤ Nat.card A := by
    have hmul : (2 * Nat.card A') * Mlab ≤ Nat.card A * Mlab := by
      calc (2 * Nat.card A') * Mlab
          = 2 * (Nat.card A' * Mlab) := by ring
        _ = 2 * (Nat.card A * gstar) := by rw [hcard_rel]
        _ = Nat.card A * (2 * gstar) := by ring
        _ ≤ Nat.card A * Mlab := Nat.mul_le_mul_left _ h2g_le
    exact Nat.le_of_mul_le_mul_right hmul hM_pos
  exact ⟨hg_lt, h2A'_le⟩
