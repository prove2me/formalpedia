-- Prove2me | solution 1 for CompOT.SinkhornConv.theorem_4_2_sinkhorn_global_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:25:03.691404+00:00
-- url     : https://prove2.me/submissions/4e955636-db17-4ef3-878c-78e2e2d7ef19

import Mathlib
import Definitions.Def_CompOT_SinkhornConv_hilbertDist
import Definitions.Def_CompOT_SinkhornConv_birkhoffLambda
import Definitions.Def_CompOT_SinkhornConv_couplings
import Definitions.Def_CompOT_SinkhornConv_entropicObjective
import Definitions.Def_CompOT_SinkhornConv_gibbsKernel
import Definitions.Def_CompOT_SinkhornConv_IsSinkhornRun
import Theorems.Thm_CompOT_Sinkhorn_theorem_4_1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Matrix Filter

namespace SinkE1B

open CompOT.SinkhornConv

section Hilbert
variable {ι : Type*} [Fintype ι]

/-- log-ratio vector `log x - log y`. -/
noncomputable def lf (x y : ι → ℝ) (i : ι) : ℝ := Real.log (x i) - Real.log (y i)

lemma ratio_log {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (i j : ι) :
    Real.log (x i * y j / (x j * y i)) = lf x y i - lf x y j := by
  have := hx i; have := hx j; have := hy i; have := hy j
  unfold lf
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring

lemma ratio_pos {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (i j : ι) :
    0 < x i * y j / (x j * y i) := by
  have := hx i; have := hx j; have := hy i; have := hy j; positivity

lemma ratio_le_sup (x y : ι → ℝ) (i j : ι) :
    x i * y j / (x j * y i) ≤ ⨆ i, ⨆ j, x i * y j / (x j * y i) := by
  calc x i * y j / (x j * y i) ≤ ⨆ j', x i * y j' / (x j' * y i) :=
        le_ciSup (Finite.bddAbove_range (fun j' => x i * y j' / (x j' * y i))) j
    _ ≤ ⨆ i', ⨆ j', x i' * y j' / (x j' * y i') :=
        le_ciSup (Finite.bddAbove_range (fun i' => ⨆ j', x i' * y j' / (x j' * y i'))) i

lemma le_dH {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (i j : ι) :
    lf x y i - lf x y j ≤ hilbertDist x y := by
  unfold hilbertDist
  rw [← ratio_log hx hy i j]
  exact Real.log_le_log (ratio_pos hx hy i j) (ratio_le_sup x y i j)

lemma dH_le [Nonempty ι] {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) {c : ℝ}
    (h : ∀ i j, lf x y i - lf x y j ≤ c) : hilbertDist x y ≤ c := by
  unfold hilbertDist
  have hpos : 0 < ⨆ i, ⨆ j, x i * y j / (x j * y i) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact lt_of_lt_of_le (ratio_pos hx hy i i) (ratio_le_sup x y i i)
  rw [Real.log_le_iff_le_exp hpos]
  refine ciSup_le fun i => ciSup_le fun j => ?_
  rw [← Real.exp_log (ratio_pos hx hy i j), ratio_log hx hy i j]
  exact Real.exp_le_exp.2 (h i j)

lemma dH_nonneg [Nonempty ι] {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    0 ≤ hilbertDist x y := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  simpa using le_dH hx hy i i

lemma dH_eq_of [Nonempty ι] {x y x' y' : ι → ℝ} (hx' : ∀ i, 0 < x' i) (hy' : ∀ i, 0 < y' i)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (s : ℝ) (h : ∀ i, lf x' y' i = lf x y i + s) :
    hilbertDist x' y' = hilbertDist x y := by
  refine le_antisymm (dH_le hx' hy' fun i j => ?_) (dH_le hx hy fun i j => ?_)
  · rw [h i, h j]; linarith [le_dH hx hy i j]
  · linarith [le_dH hx' hy' i j, h i, h j]

lemma dH_symm [Nonempty ι] {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    hilbertDist y x = hilbertDist x y := by
  refine le_antisymm (dH_le hy hx fun i j => ?_) (dH_le hx hy fun i j => ?_)
  · have := le_dH hx hy j i; unfold lf at *; linarith
  · have := le_dH hy hx j i; unfold lf at *; linarith

lemma dH_triangle [Nonempty ι] {x y z : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hz : ∀ i, 0 < z i) : hilbertDist x z ≤ hilbertDist x y + hilbertDist y z := by
  refine dH_le hx hz fun i j => ?_
  have := le_dH hx hy i j; have := le_dH hy hz i j; unfold lf at *; linarith

lemma dH_div [Nonempty ι] {c x y : ι → ℝ} (hc : ∀ i, 0 < c i) (hx : ∀ i, 0 < x i)
    (hy : ∀ i, 0 < y i) : hilbertDist (c / x) (c / y) = hilbertDist x y := by
  have h1 : ∀ i, lf (c / x) (c / y) i = lf y x i + 0 := fun i => by
    simp only [lf, Pi.div_apply]
    rw [Real.log_div (hc i).ne' (hx i).ne', Real.log_div (hc i).ne' (hy i).ne']; ring
  rw [dH_eq_of (x' := c / x) (y' := c / y) (fun i => div_pos (hc i) (hx i))
    (fun i => div_pos (hc i) (hy i)) hy hx 0 h1, dH_symm hx hy]

lemma dH_div_right [Nonempty ι] {x c z : ι → ℝ} (hx : ∀ i, 0 < x i) (hc : ∀ i, 0 < c i)
    (hz : ∀ i, 0 < z i) : hilbertDist x (c / z) = hilbertDist (x * z) c := by
  refine dH_eq_of hx (fun i => div_pos (hc i) (hz i)) (fun i => mul_pos (hx i) (hz i)) hc 0
    fun i => ?_
  simp only [lf, Pi.div_apply, Pi.mul_apply]
  rw [Real.log_div (hc i).ne' (hz i).ne', Real.log_mul (hx i).ne' (hz i).ne']; ring

lemma dH_smul [Nonempty ι] {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    hilbertDist (fun i => x i * s) (fun i => y i * t) = hilbertDist x y := by
  refine dH_eq_of (fun i => mul_pos (hx i) hs) (fun i => mul_pos (hy i) ht) hx hy
    (Real.log s - Real.log t) fun i => ?_
  simp only [lf]
  rw [Real.log_mul (hx i).ne' hs.ne', Real.log_mul (hy i).ne' ht.ne']; ring

/-- Averaging lemma: equal weighted sums force `|log x_i - log y_i| ≤ d_H(x, y)`. -/
lemma abs_lf_le [Nonempty ι] {x y c : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hc : ∀ i, 0 < c i) (hs : ∑ i, x i * c i = ∑ i, y i * c i) (i : ι) :
    |lf x y i| ≤ hilbertDist x y := by
  have h1 : ∃ j, x j ≤ y j := by
    by_contra h; simp only [not_exists, not_le] at h
    have : ∑ i, y i * c i < ∑ i, x i * c i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ =>
        mul_lt_mul_of_pos_right (h j) (hc j)
    linarith
  have h2 : ∃ j, y j ≤ x j := by
    by_contra h; simp only [not_exists, not_le] at h
    have : ∑ i, x i * c i < ∑ i, y i * c i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ =>
        mul_lt_mul_of_pos_right (h j) (hc j)
    linarith
  obtain ⟨j1, hj1⟩ := h1
  obtain ⟨j2, hj2⟩ := h2
  have e1 : lf x y j1 ≤ 0 := by unfold lf; linarith [Real.log_le_log (hx j1) hj1]
  have e2 : 0 ≤ lf x y j2 := by unfold lf; linarith [Real.log_le_log (hy j2) hj2]
  rw [abs_le]; constructor <;> linarith [le_dH hx hy i j1, le_dH hx hy j2 i]

end Hilbert

section Kernel

lemma le_eta {p q : ℕ} (K : Matrix (Fin p) (Fin q) ℝ) (i j : Fin p) (k l : Fin q) :
    K i k * K j l / (K j k * K i l) ≤ birkhoffEta K := by
  unfold birkhoffEta
  calc K i k * K j l / (K j k * K i l) ≤ ⨆ l', K i k * K j l' / (K j k * K i l') :=
        le_ciSup (Finite.bddAbove_range (fun l' => K i k * K j l' / (K j k * K i l'))) l
    _ ≤ ⨆ k', ⨆ l', K i k' * K j l' / (K j k' * K i l') :=
        le_ciSup (Finite.bddAbove_range (fun k' => ⨆ l', K i k' * K j l' / (K j k' * K i l'))) k
    _ ≤ ⨆ j', ⨆ k', ⨆ l', K i k' * K j' l' / (K j' k' * K i l') :=
        le_ciSup (Finite.bddAbove_range
          (fun j' => ⨆ k', ⨆ l', K i k' * K j' l' / (K j' k' * K i l'))) j
    _ ≤ ⨆ i', ⨆ j', ⨆ k', ⨆ l', K i' k' * K j' l' / (K j' k' * K i' l') :=
        le_ciSup (Finite.bddAbove_range
          (fun i' => ⨆ j', ⨆ k', ⨆ l', K i' k' * K j' l' / (K j' k' * K i' l'))) i

lemma eta_le {p q : ℕ} [Nonempty (Fin p)] [Nonempty (Fin q)] (K : Matrix (Fin p) (Fin q) ℝ)
    {c : ℝ} (h : ∀ i j k l, K i k * K j l / (K j k * K i l) ≤ c) : birkhoffEta K ≤ c := by
  unfold birkhoffEta
  exact ciSup_le fun i => ciSup_le fun j => ciSup_le fun k => ciSup_le fun l => h i j k l

lemma eta_transpose {p q : ℕ} [Nonempty (Fin p)] [Nonempty (Fin q)]
    (K : Matrix (Fin p) (Fin q) ℝ) : birkhoffEta Kᵀ = birkhoffEta K := by
  refine le_antisymm (eta_le Kᵀ fun i j k l => ?_) (eta_le K fun i j k l => ?_)
  · calc Kᵀ i k * Kᵀ j l / (Kᵀ j k * Kᵀ i l) = K k i * K l j / (K l i * K k j) := by
          simp only [transpose_apply]; ring
      _ ≤ _ := le_eta K k l i j
  · calc K i k * K j l / (K j k * K i l) = Kᵀ k i * Kᵀ l j / (Kᵀ l i * Kᵀ k j) := by
          simp only [transpose_apply]; ring
      _ ≤ _ := le_eta Kᵀ k l i j

lemma lam_transpose {p q : ℕ} [Nonempty (Fin p)] [Nonempty (Fin q)]
    (K : Matrix (Fin p) (Fin q) ℝ) : birkhoffLambda Kᵀ = birkhoffLambda K := by
  unfold birkhoffLambda; rw [eta_transpose]

lemma lam_nonneg {p q : ℕ} [Nonempty (Fin p)] [Nonempty (Fin q)]
    (K : Matrix (Fin p) (Fin q) ℝ) (hK : ∀ i j, 0 < K i j) : 0 ≤ birkhoffLambda K := by
  obtain ⟨i⟩ := ‹Nonempty (Fin p)›
  obtain ⟨k⟩ := ‹Nonempty (Fin q)›
  have h1 : (1 : ℝ) ≤ birkhoffEta K := by
    have := le_eta K i i k k
    rwa [div_self (by have := hK i k; positivity)] at this
  have h2 : (1 : ℝ) ≤ Real.sqrt (birkhoffEta K) := by simpa using Real.sqrt_le_sqrt h1
  unfold birkhoffLambda
  apply div_nonneg <;> linarith

lemma lam_lt_one {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (K : Matrix (Fin p) (Fin q) ℝ)
    (hK : ∀ i j, 0 < K i j) : birkhoffLambda K < 1 :=
  (CompOT.Sinkhorn.theorem_4_1 hp hq K hK 1 1 (fun _ => one_pos) (fun _ => one_pos)).2

lemma contr {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (K : Matrix (Fin p) (Fin q) ℝ)
    (hK : ∀ i j, 0 < K i j) {x y : Fin q → ℝ} (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j) :
    hilbertDist (K *ᵥ x) (K *ᵥ y) ≤ birkhoffLambda K * hilbertDist x y :=
  (CompOT.Sinkhorn.theorem_4_1 hp hq K hK x y hx hy).1

lemma mulVec_pos {p q : ℕ} [Nonempty (Fin q)] (K : Matrix (Fin p) (Fin q) ℝ)
    (hK : ∀ i j, 0 < K i j) {x : Fin q → ℝ} (hx : ∀ j, 0 < x j) (i : Fin p) :
    0 < (K *ᵥ x) i := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_pos (fun j _ => mul_pos (hK i j) (hx j)) Finset.univ_nonempty

lemma step {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (K : Matrix (Fin p) (Fin q) ℝ)
    (hK : ∀ i j, 0 < K i j) {c : Fin p → ℝ} (hc : ∀ i, 0 < c i) {x y : Fin q → ℝ}
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j) :
    hilbertDist (c / (K *ᵥ x)) (c / (K *ᵥ y)) ≤ birkhoffLambda K * hilbertDist x y := by
  haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  rw [dH_div hc (mulVec_pos K hK hx) (mulVec_pos K hK hy)]
  exact contr hp hq K hK hx hy

lemma pair_sum {p q : ℕ} (K : Matrix (Fin p) (Fin q) ℝ) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    ∑ j, y j * (Kᵀ *ᵥ x) j = ∑ i, x i * (K *ᵥ y) i := by
  simp only [mulVec, dotProduct, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma div_mul_sum {p : ℕ} {c w : Fin p → ℝ} (hw : ∀ i, 0 < w i) :
    ∑ i, (c / w) i * w i = ∑ i, c i :=
  Finset.sum_congr rfl fun i _ => div_mul_cancel₀ (c i) (hw i).ne'

lemma rowsum {p q : ℕ} (x : Fin p → ℝ) (M : Matrix (Fin p) (Fin q) ℝ) (y : Fin q → ℝ) :
    (diagonal x * M * diagonal y) *ᵥ 1 = x * (M *ᵥ y) := by
  have h1 : diagonal y *ᵥ (1 : Fin q → ℝ) = y := by ext j; simp [Matrix.mulVec_diagonal]
  ext i
  rw [← Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Pi.mul_apply]

lemma transp {p q : ℕ} (x : Fin p → ℝ) (M : Matrix (Fin p) (Fin q) ℝ) (y : Fin q → ℝ) :
    (diagonal x * M * diagonal y)ᵀ = diagonal y * Mᵀ * diagonal x := by
  rw [transpose_mul, transpose_mul, diagonal_transpose, diagonal_transpose, Matrix.mul_assoc]

lemma entry {p q : ℕ} (x : Fin p → ℝ) (M : Matrix (Fin p) (Fin q) ℝ) (y : Fin q → ℝ)
    (i : Fin p) (j : Fin q) : (diagonal x * M * diagonal y) i j = x i * M i j * y j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

lemma tendsto_div_mulVec {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (c : Fin p → ℝ)
    {x : ℕ → Fin q → ℝ} {x0 : Fin q → ℝ} (hx : Tendsto x atTop (nhds x0))
    (h0 : ∀ i, (M *ᵥ x0) i ≠ 0) :
    Tendsto (fun l => c / (M *ᵥ x l)) atTop (nhds (c / (M *ᵥ x0))) := by
  have hc : Continuous fun z : Fin q → ℝ => M *ᵥ z :=
    Continuous.matrix_mulVec (A := fun _ => M) (B := id) continuous_const continuous_id
  have hM : Tendsto (fun l => M *ᵥ x l) atTop (nhds (M *ᵥ x0)) := (hc.tendsto x0).comp hx
  rw [tendsto_pi_nhds] at hM ⊢
  intro i
  exact tendsto_const_nhds.div (hM i) (h0 i)

lemma g_nonneg {q p : ℝ} (hq : 0 ≤ q) (hp : 0 < p) :
    0 ≤ q * Real.log q - q - q * Real.log p + p := by
  rcases hq.eq_or_lt with h | hq
  · subst h; simp; linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hp hq)
  rw [Real.log_div hp.ne' hq.ne'] at h
  have key : q * (Real.log p - Real.log q) ≤ p - q := by
    calc q * (Real.log p - Real.log q) ≤ q * (p / q - 1) := mul_le_mul_of_nonneg_left h hq.le
      _ = p - q := by field_simp
  nlinarith [key]

lemma g_eq {q p : ℝ} (hq : 0 ≤ q) (hp : 0 < p)
    (h0 : q * Real.log q - q - q * Real.log p + p = 0) : q = p := by
  by_contra hne
  rcases hq.eq_or_lt with h | hq
  · subst h; simp at h0; linarith
  have hne' : p / q ≠ 1 := by
    intro h; apply hne; field_simp at h; linarith
  have h := Real.log_lt_sub_one_of_pos (div_pos hp hq) hne'
  rw [Real.log_div hp.ne' hq.ne'] at h
  have key : q * (Real.log p - Real.log q) < p - q := by
    calc q * (Real.log p - Real.log q) < q * (p / q - 1) := mul_lt_mul_of_pos_left h hq
      _ = p - q := by field_simp
  nlinarith [key]

end Kernel

end SinkE1B

open Matrix Filter SinkE1B in
open CompOT.SinkhornConv in
theorem solution {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 < a i) (ha1 : ∑ i, a i = 1) (hb : ∀ j, 0 < b j) (hb1 : ∑ j, b j = 1)
    (C : Matrix (Fin n) (Fin m) ℝ) {ε : ℝ} (hε : 0 < ε)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hrun : IsSinkhornRun (gibbsKernel C ε) a b u v) :
    let K := gibbsKernel C ε
    let lam := birkhoffLambda K
    let P : ℕ → Matrix (Fin n) (Fin m) ℝ := fun ℓ => Matrix.diagonal (u ℓ) * K * Matrix.diagonal (v ℓ)
    ∃ ustar : Fin n → ℝ, ∃ vstar : Fin m → ℝ,
      (∀ i, 0 < ustar i) ∧ (∀ j, 0 < vstar j) ∧
      Filter.Tendsto u Filter.atTop (nhds ustar) ∧ Filter.Tendsto v Filter.atTop (nhds vstar) ∧
      Asymptotics.IsBigO Filter.atTop (fun ℓ => hilbertDist (u ℓ) ustar) (fun ℓ => lam ^ (2 * ℓ)) ∧
      Asymptotics.IsBigO Filter.atTop (fun ℓ => hilbertDist (v ℓ) vstar) (fun ℓ => lam ^ (2 * ℓ)) ∧
      (∀ ℓ, 1 ≤ ℓ → hilbertDist (u ℓ) ustar ≤ hilbertDist (P ℓ *ᵥ 1) a / (1 - lam ^ 2)) ∧
      (∀ ℓ, hilbertDist (v ℓ) vstar ≤
        hilbertDist ((Matrix.diagonal (u (ℓ + 1)) * K * Matrix.diagonal (v ℓ))ᵀ *ᵥ 1) b /
          (1 - lam ^ 2)) ∧
      (∀ Q : Matrix (Fin n) (Fin m) ℝ,
        (Q ∈ couplings a b ∧ IsMinOn (entropicObjective C ε) (couplings a b) Q) ↔
          Q = Matrix.diagonal ustar * K * Matrix.diagonal vstar) ∧
      (∀ ℓ, 1 ≤ ℓ → ∀ i j,
        |Real.log (P ℓ i j) - Real.log ((Matrix.diagonal ustar * K * Matrix.diagonal vstar) i j)| ≤
          hilbertDist (u ℓ) ustar + hilbertDist (v ℓ) vstar) := by
  intro K lam P
  have hKC : ∀ i j, K i j = Real.exp (-C i j / ε) := fun i j => rfl
  change IsSinkhornRun K a b u v at hrun
  have hP : ∀ ℓ, P ℓ = diagonal (u ℓ) * K * diagonal (v ℓ) := fun _ => rfl
  have hlamdef : lam = birkhoffLambda K := rfl
  clear_value P
  clear_value lam
  clear_value K
  obtain ⟨hv0, hstep⟩ := hrun
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at ha1
    · exact h
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hb1
    · exact h
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hK : ∀ i j, 0 < K i j := fun i j => by rw [hKC]; exact Real.exp_pos _
  have hKt : ∀ i j, 0 < Kᵀ i j := fun i j => hK j i
  have hlam0 : 0 ≤ lam := by rw [hlamdef]; exact lam_nonneg K hK
  have hlam1 : lam < 1 := by rw [hlamdef]; exact lam_lt_one hn hm K hK
  have stepK : ∀ {x y : Fin m → ℝ}, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      hilbertDist (a / (K *ᵥ x)) (a / (K *ᵥ y)) ≤ lam * hilbertDist x y := by
    intro x y hx hy; rw [hlamdef]; exact step hn hm K hK ha hx hy
  have stepKt : ∀ {x y : Fin n → ℝ}, (∀ i, 0 < x i) → (∀ i, 0 < y i) →
      hilbertDist (b / (Kᵀ *ᵥ x)) (b / (Kᵀ *ᵥ y)) ≤ lam * hilbertDist x y := by
    intro x y hx hy; rw [hlamdef, ← lam_transpose K]; exact step hm hn Kᵀ hKt hb hx hy
  -- positivity of the iterates
  have hvpos : ∀ l j, 0 < v l j := by
    intro l; induction l with
    | zero => intro j; rw [hv0]; exact one_pos
    | succ l ih =>
      intro j
      have hu : ∀ i, 0 < u (l + 1) i := fun i => by
        rw [(hstep l).1]; exact div_pos (ha i) (mulVec_pos K hK ih i)
      rw [(hstep l).2]; exact div_pos (hb j) (mulVec_pos Kᵀ hKt hu j)
  have hupos : ∀ l i, 0 < u (l + 1) i := fun l i => by
    rw [(hstep l).1]; exact div_pos (ha i) (mulVec_pos K hK (hvpos l) i)
  -- successive differences
  have hU : ∀ l, hilbertDist (u (l + 1 + 1)) (u (l + 1)) ≤ lam * hilbertDist (v (l + 1)) (v l) := by
    intro l; rw [(hstep (l + 1)).1, (hstep l).1]; exact stepK (hvpos _) (hvpos _)
  have hV : ∀ l, hilbertDist (v (l + 1 + 1)) (v (l + 1)) ≤
      lam * hilbertDist (u (l + 1 + 1)) (u (l + 1)) := by
    intro l; rw [(hstep (l + 1)).2, (hstep l).2]; exact stepKt (hupos _) (hupos _)
  set D0 := hilbertDist (v 1) (v 0) with hD0
  have hD : ∀ l, hilbertDist (v (l + 1)) (v l) ≤ (lam ^ 2) ^ l * D0 := by
    intro l; induction l with
    | zero => simp [hD0]
    | succ l ih =>
      calc hilbertDist (v (l + 1 + 1)) (v (l + 1)) ≤ lam * hilbertDist (u (l + 1 + 1)) (u (l + 1)) := hV l
        _ ≤ lam * (lam * hilbertDist (v (l + 1)) (v l)) := mul_le_mul_of_nonneg_left (hU l) hlam0
        _ ≤ lam * (lam * ((lam ^ 2) ^ l * D0)) := by gcongr
        _ = (lam ^ 2) ^ (l + 1) * D0 := by ring
  have hnorm : ∀ l, ∑ j, v (l + 1) j * (Kᵀ *ᵥ u (l + 1)) j = ∑ j, v l j * (Kᵀ *ᵥ u (l + 1)) j := by
    intro l
    have e1 := div_mul_sum (c := b) (mulVec_pos Kᵀ hKt (hupos l))
    rw [← (hstep l).2] at e1
    have e2 := pair_sum K (u (l + 1)) (v l)
    have e3 := div_mul_sum (c := a) (mulVec_pos K hK (hvpos l))
    rw [← (hstep l).1] at e3
    linarith
  have habs : ∀ l j, |Real.log (v (l + 1) j) - Real.log (v l j)| ≤ (lam ^ 2) ^ l * D0 := fun l j =>
    (abs_lf_le (hvpos _) (hvpos _) (mulVec_pos Kᵀ hKt (hupos l)) (hnorm l) j).trans (hD l)
  have hcau : CauchySeq (fun l => fun j => Real.log (v l j)) := by
    refine cauchySeq_of_le_geometric (lam ^ 2) D0 (by nlinarith) fun l => ?_
    refine (dist_pi_le_iff (mul_nonneg (dH_nonneg (hvpos 1) (hvpos 0)) (pow_nonneg (sq_nonneg _) _))).2
      fun j => ?_
    show dist (Real.log (v l j)) (Real.log (v (l + 1) j)) ≤ D0 * (lam ^ 2) ^ l
    rw [Real.dist_eq, abs_sub_comm, mul_comm]; exact habs l j
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  obtain ⟨vstar, hvs_def⟩ : ∃ w : Fin m → ℝ, w = fun j => Real.exp (L j) := ⟨_, rfl⟩
  have hvs : ∀ j, 0 < vstar j := fun j => by rw [hvs_def]; exact Real.exp_pos _
  have hvlim : Tendsto v atTop (nhds vstar) := by
    rw [hvs_def]
    have h1 := ((continuous_pi fun j => Real.continuous_exp.comp (continuous_apply j)).tendsto L).comp hL
    refine h1.congr fun l => funext fun j => ?_
    exact Real.exp_log (hvpos l j)
  obtain ⟨ustar, hufix⟩ : ∃ w : Fin n → ℝ, w = a / (K *ᵥ vstar) := ⟨_, rfl⟩
  have hus : ∀ i, 0 < ustar i := fun i => by
    rw [hufix]; exact div_pos (ha i) (mulVec_pos K hK hvs i)
  have hulim1 : Tendsto (fun l => u (l + 1)) atTop (nhds ustar) := by
    rw [hufix]
    exact (tendsto_div_mulVec K a hvlim (fun i => (mulVec_pos K hK hvs i).ne')).congr
      fun l => ((hstep l).1).symm
  have hulim : Tendsto u atTop (nhds ustar) := (tendsto_add_atTop_iff_nat 1).1 hulim1
  have hvfix : vstar = b / (Kᵀ *ᵥ ustar) := by
    have h1 : Tendsto (fun l => v (l + 1)) atTop (nhds (b / (Kᵀ *ᵥ ustar))) :=
      (tendsto_div_mulVec Kᵀ b hulim1 (fun j => (mulVec_pos Kᵀ hKt hus j).ne')).congr
        fun l => ((hstep l).2).symm
    have h2 : Tendsto (fun l => v (l + 1)) atTop (nhds vstar) := (tendsto_add_atTop_iff_nat 1).2 hvlim
    exact tendsto_nhds_unique h2 h1
  -- contraction towards the limit
  have cu : ∀ l, hilbertDist (u (l + 1)) ustar ≤ lam * hilbertDist (v l) vstar := by
    intro l; rw [(hstep l).1, hufix]; exact stepK (hvpos l) hvs
  have cv : ∀ l, hilbertDist (v (l + 1)) vstar ≤ lam * hilbertDist (u (l + 1)) ustar := by
    intro l; rw [(hstep l).2, hvfix]; exact stepKt (hupos l) hus
  have cvv : ∀ l, hilbertDist (v (l + 1)) vstar ≤ lam ^ 2 * hilbertDist (v l) vstar := fun l =>
    calc _ ≤ lam * hilbertDist (u (l + 1)) ustar := cv l
      _ ≤ lam * (lam * hilbertDist (v l) vstar) := mul_le_mul_of_nonneg_left (cu l) hlam0
      _ = lam ^ 2 * hilbertDist (v l) vstar := by ring
  have cuu : ∀ l, hilbertDist (u (l + 1 + 1)) ustar ≤ lam ^ 2 * hilbertDist (u (l + 1)) ustar :=
    fun l =>
    calc _ ≤ lam * hilbertDist (v (l + 1)) vstar := cu (l + 1)
      _ ≤ lam * (lam * hilbertDist (u (l + 1)) ustar) := mul_le_mul_of_nonneg_left (cv l) hlam0
      _ = lam ^ 2 * hilbertDist (u (l + 1)) ustar := by ring
  set D := hilbertDist (v 0) vstar with hDdef
  have hvrate : ∀ l, hilbertDist (v l) vstar ≤ (lam ^ 2) ^ l * D := by
    intro l; induction l with
    | zero => simp [hDdef]
    | succ l ih =>
      calc _ ≤ lam ^ 2 * hilbertDist (v l) vstar := cvv l
        _ ≤ lam ^ 2 * ((lam ^ 2) ^ l * D) := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
        _ = (lam ^ 2) ^ (l + 1) * D := by ring
  have hurate : ∀ l, hilbertDist (u (l + 1)) ustar ≤ lam * ((lam ^ 2) ^ l * D) := fun l =>
    (cu l).trans (mul_le_mul_of_nonneg_left (hvrate l) hlam0)
  have hlam2 : 0 < 1 - lam ^ 2 := by nlinarith
  -- the limit coupling
  obtain ⟨Ps, hPsdef⟩ : ∃ X : Matrix (Fin n) (Fin m) ℝ, X = diagonal ustar * K * diagonal vstar :=
    ⟨_, rfl⟩
  have hPs_ij : ∀ i j, Ps i j = ustar i * K i j * vstar j := fun i j => by rw [hPsdef, entry]
  have hPs_pos : ∀ i j, 0 < Ps i j := fun i j => by
    rw [hPs_ij]; have := hus i; have := hK i j; have := hvs j; positivity
  have hPs_mem : Ps ∈ couplings a b := by
    refine ⟨fun i j => (hPs_pos i j).le, ?_, ?_⟩
    · rw [hPsdef, rowsum]; ext i
      rw [Pi.mul_apply, hufix]; exact div_mul_cancel₀ _ (mulVec_pos K hK hvs i).ne'
    · rw [hPsdef, transp, rowsum]; ext j
      rw [Pi.mul_apply, hvfix]; exact div_mul_cancel₀ _ (mulVec_pos Kᵀ hKt hus j).ne'
  have hrow : ∀ Q : Matrix (Fin n) (Fin m) ℝ, Q *ᵥ 1 = a → ∀ i, ∑ j, Q i j = a i := by
    intro Q hQ i; rw [← hQ]; simp [mulVec, dotProduct]
  have hcol : ∀ Q : Matrix (Fin n) (Fin m) ℝ, Qᵀ *ᵥ 1 = b → ∀ j, ∑ i, Q i j = b j := by
    intro Q hQ j; rw [← hQ]; simp [mulVec, dotProduct]
  have hobj : ∀ Q ∈ couplings a b, entropicObjective C ε Q =
      ε * (∑ i, ∑ j, (Q i j * Real.log (Q i j) - Q i j - Q i j * Real.log (Ps i j))) +
        ε * (∑ i, a i * Real.log (ustar i) + ∑ j, b j * Real.log (vstar j)) := by
    rintro Q ⟨-, hQr, hQc⟩
    have hC : ∀ i j, C i j =
        ε * (Real.log (ustar i) + Real.log (vstar j)) - ε * Real.log (Ps i j) := by
      intro i j
      have := hus i; have := hK i j; have := hvs j
      rw [hPs_ij, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), hKC, Real.log_exp]
      field_simp; ring
    have e1 : ∑ i, ∑ j, Q i j * (Real.log (ustar i) + Real.log (vstar j)) =
        ∑ i, a i * Real.log (ustar i) + ∑ j, b j * Real.log (vstar j) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, hrow Q hQr i]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, hcol Q hQc j]
    unfold entropicObjective entropy
    simp only [hC]
    rw [← e1]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hgap : ∀ Q ∈ couplings a b, entropicObjective C ε Q - entropicObjective C ε Ps =
      ε * ∑ i, ∑ j, (Q i j * Real.log (Q i j) - Q i j - Q i j * Real.log (Ps i j) + Ps i j) := by
    intro Q hQ
    rw [hobj Q hQ, hobj Ps hPs_mem]
    have e : ∀ X Y T : ℝ, (ε * X + ε * T) - (ε * Y + ε * T) = ε * (X - Y) := by intros; ring
    rw [e, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hgap_nonneg : ∀ Q ∈ couplings a b,
      0 ≤ ∑ i, ∑ j, (Q i j * Real.log (Q i j) - Q i j - Q i j * Real.log (Ps i j) + Ps i j) :=
    fun Q hQ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      g_nonneg (hQ.1 i j) (hPs_pos i j)
  refine ⟨ustar, vstar, hus, hvs, hulim, hvlim, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rate for u
    rcases hlam0.eq_or_lt with h0 | h0
    · refine Asymptotics.IsBigO.of_bound 0 (Filter.eventually_atTop.2 ⟨1, fun l hl => ?_⟩)
      obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
      have h1 := hurate k
      rw [← h0, zero_mul] at h1
      have h2 := dH_nonneg (hupos k) hus
      rw [zero_mul, Real.norm_eq_abs, abs_le]; constructor <;> linarith
    · refine Asymptotics.IsBigO.of_bound (D / lam) (Filter.eventually_atTop.2 ⟨1, fun l hl => ?_⟩)
      obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
      have h1 := hurate k
      have h2 := dH_nonneg (hupos k) hus
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h2, abs_of_nonneg (pow_nonneg hlam0 _)]
      calc _ ≤ lam * ((lam ^ 2) ^ k * D) := h1
        _ = D / lam * lam ^ (2 * (k + 1)) := by field_simp; ring
  · -- rate for v
    refine Asymptotics.IsBigO.of_bound D (Filter.Eventually.of_forall fun l => ?_)
    have h2 := dH_nonneg (hvpos l) hvs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h2, abs_of_nonneg (pow_nonneg hlam0 _),
      pow_mul]
    exact (hvrate l).trans_eq (mul_comm _ _)
  · -- bound (4.23) for u
    intro ℓ hℓ
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    have e1 : hilbertDist (u (k + 1)) (u (k + 1 + 1)) = hilbertDist (P (k + 1) *ᵥ 1) a := by
      rw [hP, rowsum, (hstep (k + 1)).1,
        dH_div_right (hupos k) ha (mulVec_pos K hK (hvpos (k + 1)))]
    have t := dH_triangle (hupos k) (hupos (k + 1)) hus
    have c2 := cuu k
    rw [le_div_iff₀ hlam2]; nlinarith
  · -- bound (4.23) for v (corrected)
    intro ℓ
    have e1 : hilbertDist (v ℓ) (v (ℓ + 1)) =
        hilbertDist ((diagonal (u (ℓ + 1)) * K * diagonal (v ℓ))ᵀ *ᵥ 1) b := by
      rw [transp, rowsum, (hstep ℓ).2, dH_div_right (hvpos ℓ) hb (mulVec_pos Kᵀ hKt (hupos ℓ))]
    have t := dH_triangle (hvpos ℓ) (hvpos (ℓ + 1)) hvs
    have c2 := cvv ℓ
    rw [le_div_iff₀ hlam2]; nlinarith
  · -- uniqueness of the entropic minimiser
    intro Q
    rw [← hPsdef]
    constructor
    · rintro ⟨hQ, hmin⟩
      have hle := isMinOn_iff.1 hmin Ps hPs_mem
      have hg := hgap Q hQ
      have hS0 := hgap_nonneg Q hQ
      have hS : ∑ i, ∑ j, (Q i j * Real.log (Q i j) - Q i j - Q i j * Real.log (Ps i j) + Ps i j)
          = 0 := by
        have : ε * ∑ i, ∑ j, (Q i j * Real.log (Q i j) - Q i j - Q i j * Real.log (Ps i j) +
            Ps i j) ≤ 0 := by linarith
        have := nonpos_of_mul_nonpos_right this hε
        linarith
      ext i j
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
        g_nonneg (hQ.1 i j) (hPs_pos i j))).1 hS i (Finset.mem_univ i)
      have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
        g_nonneg (hQ.1 i j) (hPs_pos i j))).1 hi j (Finset.mem_univ j)
      exact g_eq (hQ.1 i j) (hPs_pos i j) hij
    · rintro rfl
      refine ⟨hPs_mem, isMinOn_iff.2 fun Q hQ => ?_⟩
      have hg := hgap Q hQ
      have := mul_nonneg hε.le (hgap_nonneg Q hQ)
      linarith
  · -- (4.24)
    intro ℓ hℓ i j
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    rw [← hPsdef]
    have hcolsum : ∀ (w : Fin n → ℝ) (z : Fin m → ℝ),
        ∑ i', w i' * z j * K i' j = z j * (Kᵀ *ᵥ w) j := by
      intro w z
      simp only [mulVec, dotProduct, transpose_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i' _ => by ring
    have hv1 : v (k + 1) j * (Kᵀ *ᵥ u (k + 1)) j = b j := by
      rw [(hstep k).2]; exact div_mul_cancel₀ _ (mulVec_pos Kᵀ hKt (hupos k) j).ne'
    have hv2 : vstar j * (Kᵀ *ᵥ ustar) j = b j := by
      rw [hvfix]; exact div_mul_cancel₀ _ (mulVec_pos Kᵀ hKt hus j).ne'
    have hs : ∑ i', u (k + 1) i' * v (k + 1) j * K i' j = ∑ i', ustar i' * vstar j * K i' j := by
      rw [hcolsum, hcolsum, hv1, hv2]
    have hx : ∀ i', 0 < u (k + 1) i' * v (k + 1) j := fun i' => mul_pos (hupos k i') (hvpos _ j)
    have hy : ∀ i', 0 < ustar i' * vstar j := fun i' => mul_pos (hus i') (hvs j)
    have hab := abs_lf_le (x := fun i' => u (k + 1) i' * v (k + 1) j)
      (y := fun i' => ustar i' * vstar j) (c := fun i' => K i' j) hx hy (fun i' => hK i' j) hs i
    rw [dH_smul (hupos k) hus (hvpos _ j) (hvs j)] at hab
    have e : Real.log (P (k + 1) i j) - Real.log (Ps i j) =
        lf (fun i' => u (k + 1) i' * v (k + 1) j) (fun i' => ustar i' * vstar j) i := by
      have := hupos k i; have := hvpos (k + 1) j; have := hus i; have := hvs j; have := hK i j
      have l1 : Real.log (u (k + 1) i * K i j * v (k + 1) j) =
          Real.log (u (k + 1) i) + Real.log (K i j) + Real.log (v (k + 1) j) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      have l2 : Real.log (ustar i * K i j * vstar j) =
          Real.log (ustar i) + Real.log (K i j) + Real.log (vstar j) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      have l3 : Real.log (u (k + 1) i * v (k + 1) j) =
          Real.log (u (k + 1) i) + Real.log (v (k + 1) j) :=
        Real.log_mul (by positivity) (by positivity)
      have l4 : Real.log (ustar i * vstar j) = Real.log (ustar i) + Real.log (vstar j) :=
        Real.log_mul (by positivity) (by positivity)
      rw [hP, entry, hPs_ij]
      simp only [lf]
      rw [l1, l2, l3, l4]
      ring
    rw [e]
    have := dH_nonneg (hvpos (k + 1)) hvs
    linarith
