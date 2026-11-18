-- Prove2me | solution 1 for BirthdayEntropy.Soundness.selected_density
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:53:29.915429+00:00
-- url     : https://prove2.me/submissions/c59597c9-e583-4ef9-ac92-142367ce4d0f

import Theorems.Thm_BirthdayEntropy_Soundness_labelled_relation_count
import Theorems.Thm_BirthdayEntropy_Soundness_biclique_soundness
import Definitions.Def_BirthdayEntropy_Soundness_Biclique
noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness

private lemma oriented_edges {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ)) :
    (Finset.univ.filter (fun z : H × H => (graph φ).Adj z.1.val z.2.val)).card = 2 * (edges φ H).card := by
  classical
  let D := Finset.univ.filter (fun z : H × H => (graph φ).Adj z.1.val z.2.val)
  let f : H × H → Finset (Vertex n ℓ) := fun z => {z.1.val,z.2.val}
  have hmaps : (D : Set (H × H)).MapsTo f (edges φ H) := by
    intro z hz
    have hadj := (Finset.mem_filter.mp hz).2
    have hne := hadj.1
    change f z ∈ edges φ H
    simp only [edges, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, Finset.card_pair hne⟩, ?_⟩
    · simp [f, Finset.insert_subset_iff, z.1.property,z.2.property]
    · exact ⟨z.1.val, by simp [f], z.2.val, by simp [f], hadj⟩
  have hfiber : ∀ e ∈ edges φ H, (D.filter (fun z => f z = e)).card = 2 := by
    intro e he
    have he' := Finset.mem_filter.mp he
    have hsub := (Finset.mem_powersetCard.mp he'.1).1
    have hcard := (Finset.mem_powersetCard.mp he'.1).2
    obtain ⟨v,hv,w,hw,hadj⟩ := he'.2
    have hne := hadj.1
    have heq : e = {v,w} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · simp [Finset.insert_subset_iff,hv,hw]
      · rw [hcard,Finset.card_pair hne]
    let v' : H := ⟨v,hsub hv⟩
    let w' : H := ⟨w,hsub hw⟩
    have hne' : v' ≠ w' := by intro h; exact hne (congrArg Subtype.val h)
    have hset : D.filter (fun z => f z = e) = {(v',w'),(w',v')} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hz
        have hp : {z.1.val,z.2.val} = {v,w} := hz.2.trans heq
        have hzmem : z.1.val = v ∨ z.1.val = w := by
          have := congrArg (fun s => z.1.val ∈ s) hp
          simpa using this
        rcases hzmem with hzv | hzw
        · left
          have hzw' : z.2.val = w := by
            have hw' : w ∈ ({z.1.val,z.2.val} : Finset (Vertex n ℓ)) := by rw [hp]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
            rcases hw' with hw' | hw'
            · exact (hne (hzv.symm.trans hw'.symm)).elim
            · exact hw'.symm
          apply Prod.ext <;> apply Subtype.ext
          · exact hzv
          · exact hzw'
        · right
          have hzv' : z.2.val = v := by
            have hv' : v ∈ ({z.1.val,z.2.val} : Finset (Vertex n ℓ)) := by rw [hp]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
            rcases hv' with hv' | hv'
            · exact (hne (hv'.trans hzw)).elim
            · exact hv'.symm
          apply Prod.ext <;> apply Subtype.ext
          · exact hzw
          · exact hzv'
      · intro hz
        rcases hz with rfl | rfl
        · simp [D,f,v',w',hadj,←heq]
        · simp [D,f,v',w',(graph φ).adj_symm hadj,Finset.pair_comm,←heq]
    rw [hset,Finset.card_pair]
    intro h
    exact hne' (congrArg Prod.fst h)
  change D.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    _ = ∑ e ∈ edges φ H, 2 := Finset.sum_congr rfl hfiber
    _ = _ := by simp [Nat.mul_comm]

private lemma accepted_subtype_card {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ)) (r : ℕ) :
    (Finset.univ.filter (fun z : (Fin r → H) × (Fin r → H) => ∀ i j, (graph φ).Adj (z.1 i).val (z.2 j).val)).card =
      (accepted φ H r).card := by
  classical
  apply Finset.card_bij (fun z _ => ((fun i => (z.1 i).val),fun j => (z.2 j).val))
  · intro z hz
    simp only [accepted,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun i => (z.1 i).property,fun j => (z.2 j).property,(Finset.mem_filter.mp hz).2⟩
  · intro a ha b hb h
    apply Prod.ext <;> funext i <;> apply Subtype.ext
    · exact congrFun (congrArg Prod.fst h) i
    · exact congrFun (congrArg Prod.snd h) i
  · intro X hX
    have hX' := (Finset.mem_filter.mp hX).2
    refine ⟨((fun i => ⟨X.1 i,hX'.1 i⟩),fun j => ⟨X.2 j,hX'.2.1 j⟩),?_,rfl⟩
    simpa using hX'.2.2

private lemma birthday_biclique_lower {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ))
    (hH : 2 ≤ H.card) (r : ℕ) :
    (density φ H / 2)^(r*r) ≤ acceptanceProbability φ H r := by
  classical
  letI : Nonempty H := (Finset.card_pos.mp (by omega : 0 < H.card)).to_subtype
  have h := labelled_relation_count (fun u v : H => (graph φ).Adj u.val v.val) r
  rw [oriented_edges,accepted_subtype_card] at h
  simp only [Fintype.card_coe,Nat.cast_mul,Nat.cast_ofNat] at h
  have hHp : (0 : ℝ) < H.card := by exact_mod_cast lt_of_lt_of_le (by decide : 0<2) hH
  have hch : (0 : ℝ) < Nat.choose H.card 2 := by exact_mod_cast Nat.choose_pos hH
  have hsmall : density φ H / 2 ≤ 2 * ((edges φ H).card : ℝ) / (H.card : ℝ)^2 := by
    unfold density
    have hH2 : (2 : ℝ) ≤ H.card := by exact_mod_cast hH
    have hE : (0 : ℝ) ≤ (edges φ H).card := by positivity
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hch (by norm_num)) (sq_pos_of_pos hHp)).mpr
    rw [Nat.cast_choose_two]
    nlinarith [mul_nonneg hE (show 0 ≤ (H.card : ℝ) - 2 by linarith)]
  exact le_trans (pow_le_pow_left₀ (by unfold density; positivity) hsmall _) h

theorem solution (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε) :
    ∃ C₀ c x₀ : ℝ, 0 < C₀ ∧ 0 < c ∧ 0 < x₀ ∧ x₀ < 1/2 ∧
      ∀ (n m : ℕ) (φ : CSP n m), Source φ d → Gap φ ε →
      ∀ (ℓ : ℕ), Admitted n ℓ C₀ x₀ →
      ∀ (H : Finset (Vertex n ℓ)), H.card = Nat.choose n ℓ →
        density φ H ≤ 2 * Real.exp (-c * n * (ratio n ℓ)^3 / logScale n ℓ) := by
  classical
  obtain ⟨C₀,x₀,Cstar,c,hC₀,hx₀,hxmin,hCs,hc,hsound⟩ := biclique_soundness d ε hd hε
  have hxhalf : x₀ < 1/2 := hxmin.trans_le (min_le_right _ _)
  refine ⟨C₀,c/(Cstar+1)^2,x₀,hC₀,by positivity,hx₀,hxhalf,?_⟩
  intro n m φ hsrc hgap ℓ hadm H hH
  have hℓ : 2 ≤ ℓ := hadm.1
  have hn : 0 < (n : ℝ) := by
    by_contra h
    have hz : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    have hs := hadm.2.1
    rw [hz,mul_zero] at hs
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hx : 0 < ratio n ℓ := div_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 0<2) hℓ) hn
  have hxx : ratio n ℓ ≤ x₀ := (div_le_iff₀ hn).mpr hadm.2.1
  have hx1 : ratio n ℓ < 1 := by linarith
  have hℓn : ℓ < n := by
    have : (ℓ : ℝ) < n := by
      have := (div_lt_iff₀ hn).mp hx1
      simpa using this
    exact_mod_cast this
  have hH2 : 2 ≤ H.card := by
    rw [hH]
    have hp := Nat.choose_pos hℓn.le
    have hne : Nat.choose n ℓ ≠ 1 := by
      intro heq
      have := Nat.choose_eq_one_iff.mp heq
      omega
    omega
  have hA1 : 1 ≤ logScale n ℓ := by
    unfold logScale
    have he : Real.exp 1 ≤ Real.exp 1 / ratio n ℓ :=
      (le_div_iff₀ hx).mpr (by nlinarith [Real.exp_pos 1])
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hA : 0 < logScale n ℓ := by linarith
  let r := repetition n ℓ Cstar
  have hr : 0 < r := by
    apply Nat.ceil_pos.mpr
    positivity
  have hrc : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrupper : (r : ℝ) ≤ (Cstar+1)*logScale n ℓ/ratio n ℓ := by
    have hceil : (r : ℝ) < Cstar * logScale n ℓ / ratio n ℓ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hax : 1 ≤ logScale n ℓ / ratio n ℓ := (le_div_iff₀ hx).mpr (by linarith)
    calc
      (r : ℝ) ≤ Cstar * logScale n ℓ / ratio n ℓ + 1 := hceil.le
      _ ≤ Cstar * logScale n ℓ / ratio n ℓ + logScale n ℓ / ratio n ℓ := by linarith
      _ = _ := by ring
  by_cases hρ : 0 < density φ H
  swap
  · exact (le_of_not_gt hρ).trans (by positivity)
  have hq : 0 < density φ H / 2 := by positivity
  have hlower := birthday_biclique_lower φ H hH2 r
  have hupper := hsound n m φ hsrc hgap ℓ hadm H hH
  have hlog := Real.log_le_log (pow_pos hq (r*r)) (hlower.trans hupper)
  rw [Real.log_pow,Real.log_exp,Nat.cast_mul] at hlog
  have hlogq : Real.log (density φ H / 2) ≤ 0 := by
    have hneg : 0 < c * n * ratio n ℓ * logScale n ℓ := by positivity
    have hr2 : 0 < (r : ℝ) * r := by positivity
    nlinarith
  have hr2 : (r : ℝ)*r ≤ ((Cstar+1)*logScale n ℓ/ratio n ℓ)^2 := by
    nlinarith [sq_nonneg ((Cstar+1)*logScale n ℓ/ratio n ℓ - r)]
  have hleft := mul_le_mul_of_nonpos_right hr2 hlogq
  have heq : ((Cstar+1)*logScale n ℓ/ratio n ℓ)^2 *
      (-(c/(Cstar+1)^2) * n * (ratio n ℓ)^3 / logScale n ℓ) =
        -c * n * ratio n ℓ * logScale n ℓ := by
    field_simp
    <;> ring
  have hend : Real.log (density φ H / 2) ≤
      -(c/(Cstar+1)^2) * n * (ratio n ℓ)^3 / logScale n ℓ := by
    apply (mul_le_mul_iff_right₀ (show 0 < ((Cstar+1)*logScale n ℓ/ratio n ℓ)^2 by positivity)).mp
    rw [heq]
    exact hleft.trans hlog
  have hqbound : density φ H / 2 ≤ Real.exp (-(c/(Cstar+1)^2) * n * (ratio n ℓ)^3 / logScale n ℓ) := by
    rw [← Real.exp_log hq]
    exact Real.exp_le_exp.mpr hend
  linarith
