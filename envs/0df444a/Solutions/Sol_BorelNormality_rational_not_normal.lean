-- Prove2me | solution 1 for BorelNormality.rational_not_normal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:46:27.310597+00:00
-- url     : https://prove2.me/submissions/56fcba43-df7f-42c6-bb95-b7547a1b23e8

import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false

namespace RNNAux

open Filter Topology

lemma periodic_mul (s : ℕ → ℕ) (n0 P : ℕ) (hper : ∀ n ≥ n0, s (n + P) = s n) :
    ∀ t n, n0 ≤ n → s (n + P * t) = s n := by
  intro t
  induction t with
  | zero => intro n _; simp
  | succ t ih =>
    intro n hn
    rw [show n + P * (t + 1) = (n + P * t) + P by ring, hper _ (by omega), ih n hn]

lemma not_normal_of_periodic (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ) (n0 P : ℕ) (hP : 0 < P)
    (hper : ∀ n ≥ n0, s (n + P) = s n) : ¬ Normal.IsNormalSeq b s := by
  classical
  intro hN
  let W : ℕ → (Fin P → ℕ) := fun i j => s (i + j)
  let S : Finset (Fin P → ℕ) := (Finset.Ico n0 (n0 + P)).image W
  let T : Finset (Fin P → ℕ) := Finset.univ.image (fun f : Fin P → Fin b => fun j => (f j : ℕ))
  have hS : S.card ≤ P := by
    calc S.card ≤ (Finset.Ico n0 (n0 + P)).card := Finset.card_image_le
      _ = P := by simp
  have hT : T.card = b ^ P := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro f g hfg
      funext j
      exact Fin.ext (congrFun hfg j)
  have hlt : S.card < T.card := by
    rw [hT]
    exact lt_of_le_of_lt hS (Nat.lt_pow_self (by omega))
  obtain ⟨g, hgT, hgS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hgT
  let w : List ℕ := List.ofFn (fun j : Fin P => (f j : ℕ))
  have hw : ∀ d ∈ w, d < b := by
    intro d hd
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
    exact (f j).isLt
  have hWper : ∀ i, n0 ≤ i → W i ∈ S := by
    intro i hi
    apply Finset.mem_image.mpr
    refine ⟨n0 + (i - n0) % P, ?_, ?_⟩
    · simp only [Finset.mem_Ico]
      constructor
      · omega
      · have := Nat.mod_lt (i - n0) hP; omega
    · funext j
      simp only [W]
      have hi' : i + j = (n0 + (i - n0) % P + j) + P * ((i - n0) / P) := by
        have := Nat.mod_add_div (i - n0) P
        omega
      rw [hi', periodic_mul s n0 P hper _ _ (by omega)]
  have hcount : ∀ N, Normal.count s w N ≤ n0 := by
    intro N
    unfold Normal.count
    calc ((Finset.range N).filter (fun i => ∀ j : Fin w.length, s (i + j) = w.get j)).card
        ≤ (Finset.range n0).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          by_contra hge
          push Not at hge
          apply hgS
          have hWi := hWper i hge
          have : W i = fun j => (f j : ℕ) := by
            funext j
            have h := hi.2 (Fin.cast (by simp [w]) j)
            simp only [W]
            simp only [Fin.val_cast] at h
            rw [h]
            simp [w]
          rw [← this]; exact hWi
      _ = n0 := by simp
  have hlim := hN w hw
  have h0 : Tendsto (fun N : ℕ => (Normal.count s w N : ℝ) / N) atTop (𝓝 0) := by
    have hu : Tendsto (fun N : ℕ => (n0 : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (n0 : ℝ)
    apply squeeze_zero (fun N => by positivity) (fun N => ?_) hu
    gcongr
    exact_mod_cast hcount N
  have := tendsto_nhds_unique hlim h0
  have hpos : (0 : ℝ) < ((b : ℝ) ^ w.length)⁻¹ := by
    have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    positivity
  linarith

lemma fract_periodic (q : ℚ) (b : ℕ) (hb : 2 ≤ b) :
    ∃ n0 P : ℕ, 0 < P ∧ ∀ n ≥ n0,
      Int.fract ((q : ℝ) * (b : ℝ) ^ (n + P)) = Int.fract ((q : ℝ) * (b : ℝ) ^ n) := by
  have : NeZero q.den := ⟨q.den_nz⟩
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => ((b : ZMod q.den) ^ n))
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hfij.symm (by omega)
  refine ⟨i, j - i, by omega, fun n hn => ?_⟩
  have hd : (q.den : ℤ) ∣ (b : ℤ) ^ j - (b : ℤ) ^ i := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    exact hfij
  obtain ⟨K, hK⟩ := hd
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have heq : (q : ℝ) * (b : ℝ) ^ (n + (j - i)) =
      (q : ℝ) * (b : ℝ) ^ n + ((q.num * K * (b : ℤ) ^ (n - i) : ℤ) : ℝ) := by
    have hK' : ((b : ℝ) ^ j - (b : ℝ) ^ i) = (q.den : ℝ) * K := by exact_mod_cast hK
    have hq : (q : ℝ) = (q.num : ℝ) / q.den := by
      rw [← Rat.num_div_den q]; push_cast; rw [Rat.num_div_den]
    have e1 : (b : ℝ) ^ (n + (j - i)) = (b : ℝ) ^ (n - i) * (b : ℝ) ^ j := by
      rw [← pow_add]; congr 1; omega
    have e2 : (b : ℝ) ^ n = (b : ℝ) ^ (n - i) * (b : ℝ) ^ i := by
      rw [← pow_add]; congr 1; omega
    rw [e1, e2]
    push_cast
    rw [hq]
    field_simp
    have : (b : ℝ) ^ j = (b : ℝ) ^ i + (q.den : ℝ) * K := by linarith
    rw [this]
  rw [heq, Int.fract_add_intCast]

lemma digit_eq (b : ℕ) (x : ℝ) (n : ℕ) :
    Normal.digit b x n = (⌊Int.fract (x * (b : ℝ) ^ n) * b⌋ % (b : ℤ)).toNat := by
  unfold Normal.digit
  congr 1
  have : x * (b : ℝ) ^ (n + 1) = Int.fract (x * (b : ℝ) ^ n) * b + ((⌊x * (b : ℝ) ^ n⌋ * b : ℤ) : ℝ) := by
    push_cast
    rw [Int.fract]
    ring
  rw [this, Int.floor_add_intCast, Int.add_mul_emod_self_right]

end RNNAux

open RNNAux in
theorem solution (q : ℚ) (b : ℕ) (hb : 2 ≤ b) :
    ¬ Normal.IsNormalReal b (q : ℝ) := by
  obtain ⟨n0, P, hP, hper⟩ := fract_periodic q b hb
  apply not_normal_of_periodic b hb _ n0 P hP
  intro n hn
  rw [digit_eq, digit_eq, show n + P = n + P from rfl, hper n hn]
