-- Prove2me | solution 1 for BurerMonteiro.RankIncrease.prop_2_5_rank_increase_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T18:09:01.746611+00:00
-- url     : https://prove2.me/submissions/23b5cbba-eb44-4f72-9fbf-01fa76757ad3

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.Frobenius

namespace C3B
open BurerMonteiro.RankIncrease Filter Topology

lemma frob_eq_sum {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) ℝ) :
    frob X Y = ∑ a, ∑ k, X a k * Y a k := by
  simp only [frob, trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

lemma frob_comm {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) ℝ) : frob X Y = frob Y X := by
  rw [frob_eq_sum, frob_eq_sum]; simp [mul_comm]

lemma frob_add_left {p q : ℕ} (X X' Y : Matrix (Fin p) (Fin q) ℝ) :
    frob (X + X') Y = frob X Y + frob X' Y := by
  simp [frob, transpose_add, Matrix.add_mul, trace_add]

lemma frob_add_right {p q : ℕ} (X Y Y' : Matrix (Fin p) (Fin q) ℝ) :
    frob X (Y + Y') = frob X Y + frob X Y' := by
  simp [frob, Matrix.mul_add, trace_add]

lemma frob_smul_left {p q : ℕ} (s : ℝ) (X Y : Matrix (Fin p) (Fin q) ℝ) :
    frob (s • X) Y = s * frob X Y := by
  simp [frob, transpose_smul, Matrix.smul_mul, trace_smul]

lemma frob_smul_right {p q : ℕ} (s : ℝ) (X Y : Matrix (Fin p) (Fin q) ℝ) :
    frob X (s • Y) = s * frob X Y := by
  simp [frob, Matrix.mul_smul, trace_smul]

lemma frob_sub_left {p q : ℕ} (X X' Y : Matrix (Fin p) (Fin q) ℝ) :
    frob (X - X') Y = frob X Y - frob X' Y := by
  simp [frob, transpose_sub, Matrix.sub_mul, trace_sub]

lemma frob_sum_left {p q : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin p) (Fin q) ℝ)
    (Y : Matrix (Fin p) (Fin q) ℝ) : frob (∑ i ∈ s, f i) Y = ∑ i ∈ s, frob (f i) Y := by
  simp [frob, transpose_sum, Matrix.sum_mul, trace_sum]

lemma frob_sum_right {p q : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin p) (Fin q) ℝ)
    (X : Matrix (Fin p) (Fin q) ℝ) : frob X (∑ i ∈ s, f i) = ∑ i ∈ s, frob X (f i) := by
  simp [frob, Matrix.mul_sum, trace_sum]

lemma frob_zero_left {p q : ℕ} (Y : Matrix (Fin p) (Fin q) ℝ) : frob 0 Y = 0 := by
  simp [frob]

lemma frob_mul_transpose {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (X Y : Matrix (Fin n) (Fin r) ℝ) :
    frob A (X * Yᵀ) = frob (A * Y) X := by
  unfold frob
  rw [transpose_mul, ← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]

lemma frob_mul_left {n r : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (X Y : Matrix (Fin n) (Fin r) ℝ) :
    frob X (S * Y) = frob (Sᵀ * X) Y := by
  simp [frob, transpose_mul, Matrix.mul_assoc]

lemma frob_transpose_of_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (M : Matrix (Fin n) (Fin n) ℝ) : frob A Mᵀ = frob A M := by
  unfold frob
  rw [hA.eq, ← trace_transpose, transpose_mul, transpose_transpose, hA.eq, trace_mul_comm]

lemma frob_vecMulVec {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    frob S (vecMulVec u u) = u ⬝ᵥ (S *ᵥ u) := by
  rw [frob_eq_sum]
  simp only [vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma frob_nonneg_of_psd {n : ℕ} (S X : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (hX : X.PosSemidef) : 0 ≤ frob S X := by
  obtain ⟨k, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hX
  rw [frob_sum_right]
  refine Finset.sum_nonneg fun i _ => ?_
  have := hS.dotProduct_mulVec_nonneg (v i)
  simp only [star_trivial] at this ⊢
  rw [frob_vecMulVec]; exact this

/-- the frobenius identity `C • X = S(y) • X + ∑ yᵢ Aᵢ • X` -/
lemma frob_C_eq {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (y : Fin m → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    frob C X = frob (slack C A y) X + ∑ i, y i * frob (A i) X := by
  simp only [slack, frob_sub_left, frob_sum_left, frob_smul_left]
  ring


def Emat {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin n) (Fin r) ℝ)
    (c : Fin m → ℝ) : Matrix (Fin n) (Fin r) ℝ := ∑ j, c j • (A j * R)

def Gm {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) (c : Fin m → ℝ) : Fin m → ℝ :=
  fun i => frob (A i) ((R + Emat A R c) * (R + Emat A R c)ᵀ) - b i

lemma Gm_contDiff {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) : ContDiff ℝ 1 (Gm A b R) := by
  have : Gm A b R = fun c i => (∑ a, ∑ a', A i a a' * ∑ k,
      (R a k + ∑ j, c j * (A j * R) a k) * (R a' k + ∑ j, c j * (A j * R) a' k)) - b i := by
    funext c i
    simp [Gm, Emat, frob_eq_sum, mul_apply, transpose_apply, Matrix.sum_apply]
  rw [this]
  fun_prop


lemma Emat_smul {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin n) (Fin r) ℝ)
    (s : ℝ) (c : Fin m → ℝ) : Emat A R (s • c) = s • Emat A R c := by
  simp [Emat, Finset.smul_sum, smul_smul]

lemma Emat_zero {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin n) (Fin r) ℝ) :
    Emat A R 0 = 0 := by
  simp [Emat]

lemma Gm_line {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) (hA : ∀ i, (A i).IsSymm) (c : Fin m → ℝ) (s : ℝ) :
    Gm A b R (s • c) = fun i => Gm A b R 0 i + s * (2 * frob (A i * R) (Emat A R c)) +
      s ^ 2 * frob (A i) (Emat A R c * (Emat A R c)ᵀ) := by
  funext i
  have hexp : (R + s • Emat A R c) * (R + s • Emat A R c)ᵀ = R * Rᵀ + s • (Emat A R c * Rᵀ) +
      s • (R * (Emat A R c)ᵀ) + (s ^ 2) • (Emat A R c * (Emat A R c)ᵀ) := by
    simp only [transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, sq]
    module
  have h2 : frob (A i) (R * (Emat A R c)ᵀ) = frob (A i * R) (Emat A R c) := by
    rw [← frob_transpose_of_symm _ (hA i), transpose_mul, transpose_transpose, frob_mul_transpose]
  have h3 : frob (A i) (Emat A R c * Rᵀ) = frob (A i * R) (Emat A R c) := frob_mul_transpose _ _ _
  simp only [Gm, Emat_smul, Emat_zero, add_zero, hexp, frob_add_right, frob_smul_right, h2, h3]
  ring

lemma Gm_fderiv {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) (hA : ∀ i, (A i).IsSymm) (c : Fin m → ℝ) :
    fderiv ℝ (Gm A b R) 0 c = fun i => 2 * frob (A i * R) (Emat A R c) := by
  have hd : HasFDerivAt (Gm A b R) (fderiv ℝ (Gm A b R) 0) ((0 : ℝ) • c) := by
    rw [zero_smul]
    exact ((Gm_contDiff A b R).differentiable one_ne_zero 0).hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => s • c) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const c
  have h1 := hd.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun s : ℝ => Gm A b R (s • c))
      (fun i => 2 * frob (A i * R) (Emat A R c)) 0 := by
    simp_rw [Gm_line A b R hA]
    rw [hasDerivAt_pi]
    intro i
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (2 * frob (A i * R) (Emat A R c))).const_add
      (Gm A b R 0 i)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const
        (frob (A i) (Emat A R c * (Emat A R c)ᵀ)))
    convert this using 1
    · funext x; simp
    · simp
  exact h1.unique h2

lemma Gm_fderiv_inj {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) (hA : ∀ i, (A i).IsSymm) (hreg : IsRegular A R) :
    Function.Injective (fderiv ℝ (Gm A b R) 0) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
  have hi : ∀ i, frob (A i * R) (Emat A R c) = 0 := by
    intro i
    have := congrFun ((Gm_fderiv A b R hA c).symm.trans hc) i
    simpa using this
  have hEE : frob (Emat A R c) (Emat A R c) = 0 := by
    show frob (∑ j, c j • (A j * R)) (Emat A R c) = 0
    rw [frob_sum_left]
    simp [frob_smul_left, hi]
  have hE : Emat A R c = 0 := by
    rw [frob_eq_sum] at hEE
    ext a k
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun k _ =>
      mul_self_nonneg _)).1 hEE a (Finset.mem_univ _)
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg _)).1 h k
      (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 h'
  funext j
  exact Fintype.linearIndependent_iff.1 hreg c hE j

lemma exists_strict {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) (hA : ∀ i, (A i).IsSymm) (hreg : IsRegular A R) :
    ∃ e : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ), HasStrictFDerivAt (Gm A b R)
      (e : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) 0 := by
  have hinj := Gm_fderiv_inj A b R hA hreg
  have hsurj : Function.Surjective (fderiv ℝ (Gm A b R) 0) := by
    have := LinearMap.injective_iff_surjective (f := ((fderiv ℝ (Gm A b R) 0 :
      (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)))
    exact this.1 hinj
  refine ⟨ContinuousLinearEquiv.ofBijective (fderiv ℝ (Gm A b R) 0)
    (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj), ?_⟩
  rw [ContinuousLinearEquiv.coe_ofBijective]
  exact (Gm_contDiff A b R).contDiffAt.hasStrictFDerivAt one_ne_zero

lemma quad_bound {n m r : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) : ∃ Kq : ℝ, 0 ≤ Kq ∧ ∀ c : Fin m → ℝ,
      |frob (S * Emat A R c) (Emat A R c)| ≤ Kq * ‖c‖ ^ 2 := by
  refine ⟨∑ j, ∑ k, |frob (S * (A k * R)) (A j * R)|, by positivity, fun c => ?_⟩
  have hexp : frob (S * Emat A R c) (Emat A R c) =
      ∑ j, ∑ k, c j * c k * frob (S * (A k * R)) (A j * R) := by
    simp only [Emat, Matrix.mul_sum, Matrix.mul_smul, frob_sum_left, frob_sum_right,
      frob_smul_left, frob_smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hexp, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul]
  have hj : |c j| ≤ ‖c‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm c j
  have hk : |c k| ≤ ‖c‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm c k
  have h1 := mul_le_mul hj hk (abs_nonneg _) (norm_nonneg _)
  have ht := abs_nonneg (frob (S * (A k * R)) (A j * R))
  have h2 := mul_le_mul_of_nonneg_right h1 ht
  nlinarith

def Qmk {n r : ℕ} (P : Matrix (Fin n) (Fin r) ℝ) (d : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin (r + 1)) ℝ :=
  Matrix.of fun a j => Fin.lastCases (t * d a) (fun k => P a k) j

lemma Qmk_mul {n r : ℕ} (P : Matrix (Fin n) (Fin r) ℝ) (d : Fin n → ℝ) (t : ℝ) :
    Qmk P d t * (Qmk P d t)ᵀ = P * Pᵀ + (t * t) • vecMulVec d d := by
  ext a b
  simp [Qmk, mul_apply, Fin.sum_univ_castSucc, vecMulVec_apply]
  ring

lemma Qmk_zero {n r : ℕ} (R : Matrix (Fin n) (Fin r) ℝ) (d : Fin n → ℝ) :
    Qmk R d 0 = inject R := by
  ext a j
  induction j using Fin.lastCases <;> simp [Qmk, inject]

lemma inject_mul {n r : ℕ} (R : Matrix (Fin n) (Fin r) ℝ) : inject R * (inject R)ᵀ = R * Rᵀ := by
  rw [← Qmk_zero R 0, Qmk_mul]; simp

lemma Qmk_cont {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin n) (Fin r) ℝ)
    (d : Fin n → ℝ) :
    Continuous (fun p : ℝ × (Fin m → ℝ) => Qmk (R + Emat A R p.2) d p.1) := by
  refine continuous_pi fun a => continuous_pi fun j => ?_
  induction j using Fin.lastCases with
  | last => simp only [Qmk, of_apply, Fin.lastCases_last]; fun_prop
  | cast k =>
    simp only [Qmk, of_apply, Fin.lastCases_castSucc, Emat, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    fun_prop

lemma slack_psd {n m r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m → ℝ) (hC : C.IsSymm) (hA : ∀ i, (A i).IsSymm) (R : Matrix (Fin n) (Fin r) ℝ)
    (hfeas : ∀ i, frob (A i) (R * Rᵀ) = b i) (hreg : IsRegular A R) (y : Fin m → ℝ)
    (hy : slack C A y * R = 0) (hinj : IsNrLocalMin C A b (inject R)) :
    (slack C A y).PosSemidef := by
  set S := slack C A y with hSdef
  have hSsym : Sᵀ = S := by
    simp only [hSdef, slack, transpose_sub, transpose_sum, transpose_smul, hC.eq, (hA _).eq]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hSsym
  intro d
  simp only [star_trivial]
  by_contra hneg
  push_neg at hneg
  set w := frob S (vecMulVec d d) with hw
  have hw0 : w < 0 := by rw [hw, frob_vecMulVec]; exact hneg
  set v : Fin m → ℝ := fun i => frob (A i) (vecMulVec d d) with hv
  obtain ⟨e, hstrict⟩ := exists_strict A b R hA hreg
  set G := Gm A b R with hGdef
  have hG0 : G 0 = 0 := by
    funext i; simp [G, Gm, Emat_zero, hfeas]
  set g := hstrict.localInverse G e 0 with hgdef
  have hg_img : g 0 = 0 := by
    have := hstrict.localInverse_apply_image; rwa [hG0] at this
  have hg_right : ∀ᶠ z in 𝓝 0, G (g z) = z := by
    have := hstrict.eventually_right_inverse; rwa [hG0] at this
  have hg_bigO : (fun z => g z - g 0) =O[𝓝 0] (fun z => z - 0) := by
    have := hstrict.to_localInverse.hasFDerivAt.isBigO_sub; rwa [hG0] at this
  have hg_cont : ContinuousAt g 0 := by
    have := hstrict.localInverse_continuousAt; rwa [hG0] at this
  set z : ℝ → (Fin m → ℝ) := fun τ => (-τ) • v with hzdef
  have hz : Tendsto z (𝓝[>] 0) (𝓝 0) := by
    have h := (show Continuous z by fun_prop).tendsto 0
    rw [show z 0 = 0 by simp [z]] at h
    exact h.mono_left nhdsWithin_le_nhds
  set c : ℝ → (Fin m → ℝ) := fun τ => g (z τ) with hcdef
  have hc : Tendsto c (𝓝[>] 0) (𝓝 0) := by
    have h2 := hg_cont.tendsto.comp hz
    rwa [hg_img] at h2
  have E1 : ∀ᶠ τ in 𝓝[>] 0, G (c τ) = z τ := hz.eventually hg_right
  obtain ⟨K, hK⟩ := (hg_bigO.comp_tendsto hz).bound
  obtain ⟨Kq, hKq0, hKq⟩ := quad_bound S A R
  have E4 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Set.Ioi (0 : ℝ) := self_mem_nhdsWithin
  have E5 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), Kq * K ^ 2 * ‖v‖ ^ 2 * τ + w < 0 := by
    have h : Tendsto (fun τ : ℝ => Kq * K ^ 2 * ‖v‖ ^ 2 * τ + w) (𝓝[>] 0) (𝓝 w) := by
      have h0 := ((continuous_const.mul continuous_id).add continuous_const).tendsto (0 : ℝ)
        (f := fun τ : ℝ => Kq * K ^ 2 * ‖v‖ ^ 2 * τ + w)
      simpa using h0.mono_left nhdsWithin_le_nhds
    exact h.eventually (Iio_mem_nhds hw0)
  set Qf : ℝ → Matrix (Fin n) (Fin (r + 1)) ℝ := fun τ => Qmk (R + Emat A R (c τ)) d (√τ)
    with hQf
  have hfeasQ : ∀ τ, 0 < τ → G (c τ) = z τ → Qf τ ∈ nrFeasible A b (r + 1) := by
    intro τ hτ hG i
    have hi := congrFun hG i
    simp only [G, Gm, z, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Qf, Qmk_mul, frob_add_right, frob_smul_right, Real.mul_self_sqrt hτ.le]
    have : frob (A i) (vecMulVec d d) = v i := rfl
    rw [this]
    linarith
  have hQt : Tendsto Qf (𝓝[>] 0) (𝓝 (inject R)) := by
    have hpair : Tendsto (fun τ => (√τ, c τ)) (𝓝[>] 0) (𝓝 ((0 : ℝ), (0 : Fin m → ℝ))) := by
      have hs := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rw [Real.sqrt_zero] at hs
      exact hs.prodMk_nhds hc
    have h := ((Qmk_cont A R d).tendsto ((0 : ℝ), (0 : Fin m → ℝ))).comp hpair
    have h' : Tendsto Qf (𝓝[>] 0) (𝓝 (Qmk (R + Emat A R (0 : Fin m → ℝ)) d 0)) := h
    have e0 : Qmk (R + Emat A R (0 : Fin m → ℝ)) d 0 = inject R := by
      rw [Emat_zero, add_zero, Qmk_zero]
    rwa [e0] at h'
  have hQw : Tendsto Qf (𝓝[>] 0) (𝓝[nrFeasible A b (r + 1)] (inject R)) :=
    tendsto_nhdsWithin_iff.2 ⟨hQt, (E1.and E4).mono fun τ h => hfeasQ τ h.2 h.1⟩
  have E3 := hQw.eventually hinj.2
  obtain ⟨τ, h1, h2, h3, h4, h5⟩ := (E1.and (hK.and (E3.and (E4.and E5)))).exists
  have hτ : 0 < τ := h4
  -- the objective identity
  have hfeasτ := hfeasQ τ hτ h1
  have hRR : frob S (R * Rᵀ) = 0 := by rw [frob_mul_transpose, hy, frob_zero_left]
  have hobj : 0 ≤ frob S (Qf τ * (Qf τ)ᵀ) := by
    have h3' : frob C (R * Rᵀ) ≤ frob C (Qf τ * (Qf τ)ᵀ) := by
      simpa [nrObjective, inject_mul] using h3
    rw [frob_C_eq C A y, frob_C_eq C A y (Qf τ * (Qf τ)ᵀ), hRR] at h3'
    have : ∀ i, frob (A i) (Qf τ * (Qf τ)ᵀ) = frob (A i) (R * Rᵀ) := fun i =>
      (hfeasτ i).trans (hfeas i).symm
    simp only [this] at h3'
    linarith
  set E := Emat A R (c τ) with hEdef
  have hsplit : frob S (Qf τ * (Qf τ)ᵀ) = frob (S * E) E + τ * w := by
    simp only [Qf, Qmk_mul, frob_add_right, frob_smul_right, Real.mul_self_sqrt hτ.le]
    rw [frob_mul_transpose, Matrix.mul_add, hy, zero_add, frob_add_right, frob_comm (S * E) R,
      frob_mul_left, hSsym, hy, frob_zero_left, zero_add]
  have hcb : ‖c τ‖ ≤ K * (τ * ‖v‖) := by
    have h2' : ‖c τ‖ ≤ K * ‖z τ‖ := by simpa [hg_img] using h2
    have hzn : ‖z τ‖ = τ * ‖v‖ := by
      simp only [z, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hτ]
    rwa [hzn] at h2'
  have hq := hKq (c τ)
  have hsq : ‖c τ‖ ^ 2 ≤ (K * (τ * ‖v‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcb 2
  have hfin : frob (S * E) E + τ * w < 0 := by
    have h6 : frob (S * E) E ≤ Kq * (K * (τ * ‖v‖)) ^ 2 :=
      (le_abs_self _).trans (hq.trans (mul_le_mul_of_nonneg_left hsq hKq0))
    have h7 : Kq * (K * (τ * ‖v‖)) ^ 2 + τ * w = τ * (Kq * K ^ 2 * ‖v‖ ^ 2 * τ + w) := by ring
    have h8 : τ * (Kq * K ^ 2 * ‖v‖ ^ 2 * τ + w) < 0 := mul_neg_of_pos_of_neg hτ h5
    linarith
  linarith

end C3B

open Matrix BurerMonteiro.RankIncrease in
theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) (hsa : StandingAssumptions C A b) {r : ℕ} (hr0 : 0 < r)
    (hrn : r < n) (R : Matrix (Fin n) (Fin r) ℝ) (hloc : IsNrLocalMin C A b R)
    (hreg : IsRegular A R) (y : Fin m → ℝ) (hy : slack C A y * R = 0)
    (hinj : IsNrLocalMin C A b (inject R)) :
    IsPrimalOptimal C A b (R * Rᵀ) ∧ IsDualOptimal C A b (slack C A y) y := by
  have hfeas : ∀ i, frob (A i) (R * Rᵀ) = b i := hloc.1
  have hS : (slack C A y).PosSemidef := C3B.slack_psd C A b hC hA R hfeas hreg y hy hinj
  have hRpsd : (R * Rᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose R
  have hsum : ∀ y' : Fin m → ℝ, ∑ i, y' i * frob (A i) (R * Rᵀ) = b ⬝ᵥ y' := by
    intro y'; simp only [hfeas, dotProduct]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hval : frob C (R * Rᵀ) = b ⬝ᵥ y := by
    rw [C3B.frob_C_eq C A y, C3B.frob_mul_transpose, hy, C3B.frob_zero_left, zero_add, hsum]
  refine ⟨⟨⟨hRpsd, hfeas⟩, fun X' hX' => ?_⟩, ⟨⟨rfl, hS⟩, fun S' y' hS' => ?_⟩⟩
  · rw [hval, C3B.frob_C_eq C A y X']
    have h1 : ∑ i, y i * frob (A i) X' = b ⬝ᵥ y := by
      simp only [hX'.2, dotProduct]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 := C3B.frob_nonneg_of_psd _ _ hS hX'.1
    linarith
  · obtain ⟨rfl, hS'⟩ := hS'
    have h1 := C3B.frob_C_eq C A y' (R * Rᵀ)
    have h2 := C3B.frob_nonneg_of_psd _ _ hS' hRpsd
    rw [hsum] at h1
    linarith
