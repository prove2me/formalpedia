-- Prove2me | solution 2 for BookProof.FockSecondQuantization.dGammaOp_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:31:50.337531+00:00
-- url     : https://prove2.me/submissions/107c7c4f-7048-49f8-9c4d-7fc5e3176992

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean -/
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert
noncomputable section
@[simp] theorem up_self (j : ℕ) (α : Conf) : up j α j = α j + 1 := by
  simp [up]

theorem up_of_ne {i j : ℕ} (α : Conf) (h : i ≠ j) : up j α i = α i := by
  simp [up, Finsupp.update_apply, h]

@[simp] theorem dn_self (j : ℕ) (α : Conf) : dn j α j = α j - 1 := by
  simp [dn]

theorem dn_of_ne {i j : ℕ} (α : Conf) (h : i ≠ j) : dn j α i = α i := by
  simp [dn, Finsupp.update_apply, h]

@[simp] theorem dn_up (j : ℕ) (α : Conf) : dn j (up j α) = α := by
  refine Finsupp.ext fun i => ?_
  by_cases h : i = j
  · subst h; simp
  · rw [dn_of_ne _ h, up_of_ne _ h]

theorem up_dn (j : ℕ) {α : Conf} (h : 1 ≤ α j) : up j (dn j α) = α := by
  refine Finsupp.ext fun i => ?_
  by_cases hi : i = j
  · subst hi; simp; omega
  · rw [up_of_ne _ hi, dn_of_ne _ hi]

theorem up_injective (j : ℕ) : Function.Injective (up j) := by
  intro α β h
  have := congrArg (dn j) h
  simpa using this

theorem support_up (j : ℕ) (α : Conf) : (up j α).support ⊆ insert j α.support := by
  intro i hi
  by_cases h : i = j
  · simp [h]
  · have : α i ≠ 0 := by
      have := Finsupp.mem_support_iff.mp hi
      rwa [up_of_ne _ h] at this
    exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr this)

theorem support_dn (j : ℕ) (α : Conf) : (dn j α).support ⊆ α.support := by
  intro i hi
  have hi' := Finsupp.mem_support_iff.mp hi
  by_cases h : i = j
  · subst h
    rw [dn_self] at hi'
    exact Finsupp.mem_support_iff.mpr (by omega)
  · rw [dn_of_ne _ h] at hi'
    exact Finsupp.mem_support_iff.mpr hi'

@[simp] theorem annA_single (j : ℕ) (β : Conf) (c : ℂ) :
    annA j (Finsupp.single β c) = c • Finsupp.single (dn j β) ((Real.sqrt (β j) : ℝ) : ℂ) := by
  simp [annA, LinearMap.toSpanSingleton]

@[simp] theorem creA_single (j : ℕ) (β : Conf) (c : ℂ) :
    creA j (Finsupp.single β c)
      = c • Finsupp.single (up j β) ((Real.sqrt ((β j : ℝ) + 1) : ℝ) : ℂ) := by
  simp [creA, LinearMap.toSpanSingleton]

theorem annA_apply (j : ℕ) (u : FockAlg) (α : Conf) :
    annA j u α = ((Real.sqrt ((α j : ℝ) + 1) : ℝ) : ℂ) * u (up j α) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]; ring
  | single β c =>
    rw [annA_single]
    by_cases hb : β = up j α
    · subst hb
      simp [mul_comm]
    · have h1 : (Finsupp.single β c : FockAlg) (up j α) = 0 := by
        simp [Ne.symm hb]
      rw [h1, mul_zero]
      by_cases hj : β j = 0
      · simp [hj]
      · have hne : dn j β ≠ α := by
          intro hc
          exact hb (by rw [← hc, up_dn j (by omega)])
        simp [hne]

theorem creA_apply (j : ℕ) (u : FockAlg) (α : Conf) :
    creA j u α = ((Real.sqrt (α j) : ℝ) : ℂ) * u (dn j α) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]; ring
  | single β c =>
    rw [creA_single]
    by_cases hb : β = dn j α
    · subst hb
      by_cases hj : 1 ≤ α j
      · rw [up_dn j hj]
        have hcast : ((α j - 1 : ℕ) : ℝ) + 1 = (α j : ℝ) := by
          rw [Nat.cast_sub (R := ℝ) hj]; ring
        simp only [dn_self, hcast, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]
        rw [mul_comm]
      · have h0 : α j = 0 := by omega
        have hne : up j (dn j α) ≠ α := by
          intro hc
          have := congrArg (fun f : Conf => f j) hc
          simp at this
          omega
        simp [hne, h0]
    · have h1 : (Finsupp.single β c : FockAlg) (dn j α) = 0 := by
        simp [Ne.symm hb]
      rw [h1, mul_zero]
      have hne : up j β ≠ α := by
        intro hc
        exact hb (by rw [← hc, dn_up])
      simp [hne]

theorem ccr_annA_creA (j : ℕ) (u : FockAlg) : annA j (creA j u) - creA j (annA j u) = u := by
  refine Finsupp.ext fun α => ?_
  rw [Finsupp.sub_apply, annA_apply, creA_apply, creA_apply, annA_apply, up_self, dn_up]
  by_cases hj : 1 ≤ α j
  · have hcast : ((dn j α) j : ℝ) + 1 = (α j : ℝ) := by
      rw [dn_self, Nat.cast_sub (R := ℝ) hj]; ring
    rw [hcast, up_dn j hj]
    push_cast
    have h1 : ((Real.sqrt ((α j : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((α j : ℝ) + 1) : ℝ) : ℂ)
        = ((α j : ℝ) : ℂ) + 1 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast
      ring
    have h2 : ((Real.sqrt ((α j : ℝ)) : ℝ) : ℂ) * ((Real.sqrt ((α j : ℝ)) : ℝ) : ℂ)
        = ((α j : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    linear_combination (u α) * h1 - (u α) * h2
  · have h0 : α j = 0 := by omega
    rw [h0]
    norm_num

theorem up_dn_comm {j k : ℕ} (h : j ≠ k) (α : Conf) : dn k (up j α) = up j (dn k α) := by
  refine Finsupp.ext fun i => ?_
  by_cases hik : i = k
  · subst hik
    rw [dn_self, up_of_ne _ h.symm, up_of_ne _ h.symm, dn_self]
  · by_cases hij : i = j
    · subst hij
      rw [dn_of_ne _ hik, up_self, up_self, dn_of_ne _ hik]
    · rw [dn_of_ne _ hik, up_of_ne _ hij, up_of_ne _ hij, dn_of_ne _ hik]

theorem dn_dn_comm (j k : ℕ) (α : Conf) : dn k (dn j α) = dn j (dn k α) := by
  rcases eq_or_ne j k with rfl | h
  · rfl
  refine Finsupp.ext fun i => ?_
  by_cases hik : i = k
  · subst hik
    rw [dn_self, dn_of_ne _ h.symm, dn_of_ne _ h.symm, dn_self]
  · by_cases hij : i = j
    · subst hij
      rw [dn_of_ne _ hik, dn_self, dn_self, dn_of_ne _ hik]
    · rw [dn_of_ne _ hik, dn_of_ne _ hij, dn_of_ne _ hij, dn_of_ne _ hik]

theorem up_up_comm (j k : ℕ) (α : Conf) : up k (up j α) = up j (up k α) := by
  rcases eq_or_ne j k with rfl | h
  · rfl
  refine Finsupp.ext fun i => ?_
  by_cases hik : i = k
  · subst hik
    rw [up_self, up_of_ne _ h.symm, up_of_ne _ h.symm, up_self]
  · by_cases hij : i = j
    · subst hij
      rw [up_of_ne _ hik, up_self, up_self, up_of_ne _ hik]
    · rw [up_of_ne _ hik, up_of_ne _ hij, up_of_ne _ hij, up_of_ne _ hik]

theorem ccr_annA_creA_of_ne {j k : ℕ} (h : j ≠ k) (u : FockAlg) :
    annA j (creA k u) = creA k (annA j u) := by
  refine Finsupp.ext fun α => ?_
  rw [annA_apply, creA_apply, creA_apply, annA_apply, up_of_ne _ h.symm, dn_of_ne _ h,
    up_dn_comm h]
  ring

theorem ccr_annA_annA (j k : ℕ) (u : FockAlg) : annA j (annA k u) = annA k (annA j u) := by
  refine Finsupp.ext fun α => ?_
  rcases eq_or_ne j k with rfl | h
  · rfl
  rw [annA_apply, annA_apply, annA_apply, annA_apply, up_of_ne _ h.symm, up_of_ne _ h,
    up_up_comm]
  ring

theorem ccr_creA_creA (j k : ℕ) (u : FockAlg) : creA j (creA k u) = creA k (creA j u) := by
  refine Finsupp.ext fun α => ?_
  rcases eq_or_ne j k with rfl | h
  · rfl
  rw [creA_apply, creA_apply, creA_apply, creA_apply, dn_of_ne _ h.symm, dn_of_ne _ h,
    dn_dn_comm]
  ring

theorem support_annA (j : ℕ) (u : FockAlg) : (annA j u).support ⊆ u.support.image (dn j) := by
  intro α hα
  have hα' := Finsupp.mem_support_iff.mp hα
  rw [annA_apply] at hα'
  have hu : u (up j α) ≠ 0 := fun h => hα' (by rw [h, mul_zero])
  exact Finset.mem_image.mpr ⟨up j α, Finsupp.mem_support_iff.mpr hu, by simp⟩

theorem support_creA (j : ℕ) (u : FockAlg) : (creA j u).support ⊆ u.support.image (up j) := by
  intro α hα
  have hα' := Finsupp.mem_support_iff.mp hα
  rw [creA_apply] at hα'
  have hu : u (dn j α) ≠ 0 := fun h => hα' (by rw [h, mul_zero])
  have hj : 1 ≤ α j := by
    by_contra hc
    have h0 : α j = 0 := by omega
    exact hα' (by rw [h0]; norm_num)
  exact Finset.mem_image.mpr ⟨dn j α, Finsupp.mem_support_iff.mpr hu, up_dn j hj⟩

theorem support_subset_modes {u : FockAlg} {β : Conf} (h : β ∈ u.support) :
    β.support ⊆ modes u := fun _ hi => Finset.mem_biUnion.mpr ⟨β, h, hi⟩

theorem annA_eq_zero_of_not_mem_modes {u : FockAlg} {k : ℕ} (h : k ∉ modes u) :
    annA k u = 0 := by
  refine Finsupp.ext fun α => ?_
  rw [annA_apply, Finsupp.zero_apply]
  have hu : u (up k α) = 0 := by
    by_contra hc
    refine h (support_subset_modes (Finsupp.mem_support_iff.mpr hc) ?_)
    exact Finsupp.mem_support_iff.mpr (by rw [up_self]; omega)
  rw [hu, mul_zero]

@[simp] theorem toLp_apply (u : FockAlg) (α : Conf) : ((toLp u : Fock) : Conf → ℂ) α = u α := rfl

@[simp] theorem toLpL_apply (u : FockAlg) : toLpL u = toLp u := rfl

theorem inner_toLp_of_subset {u : FockAlg} {s : Finset Conf} (hs : u.support ⊆ s)
    (v : FockAlg) :
    (inner ℂ (toLp u) (toLp v) : ℂ) = ∑ α ∈ s, (starRingEnd ℂ) (u α) * v α := by
  rw [lp.inner_eq_tsum]
  have hcoord : ∀ α : Conf,
      (inner ℂ (((toLp u : Fock) : Conf → ℂ) α) (((toLp v : Fock) : Conf → ℂ) α) : ℂ)
        = (starRingEnd ℂ) (u α) * v α := by
    intro α
    simp [RCLike.inner_apply, mul_comm]
  rw [tsum_congr hcoord]
  refine tsum_eq_sum fun α hα => ?_
  have hu : u α = 0 := by
    by_contra hc
    exact hα (hs (Finsupp.mem_support_iff.mpr hc))
  rw [hu, map_zero, zero_mul]

theorem inner_toLp (u v : FockAlg) :
    (inner ℂ (toLp u) (toLp v) : ℂ) = ∑ α ∈ u.support, (starRingEnd ℂ) (u α) * v α :=
  inner_toLp_of_subset (Finset.Subset.refl _) v

theorem inner_creA_left (j : ℕ) (u v : FockAlg) :
    (inner ℂ (toLp (creA j u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (annA j v)) := by
  rw [inner_toLp_of_subset (support_creA j u) v, inner_toLp u (annA j v),
    Finset.sum_image (fun x _ y _ h => up_injective j h)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [creA_apply, up_self, dn_up, annA_apply]
  have hcast : ((β j + 1 : ℕ) : ℝ) = ((β j : ℝ) + 1) := by push_cast; ring
  rw [hcast, map_mul, Complex.conj_ofReal]
  ring

theorem inner_creA_right (j : ℕ) (u v : FockAlg) :
    (inner ℂ (toLp u) (toLp (creA j v)) : ℂ) = inner ℂ (toLp (annA j u)) (toLp v) := by
  have h := inner_creA_left j v u
  have := congrArg (starRingEnd ℂ) h
  rwa [inner_conj_symm, inner_conj_symm] at this

@[simp] theorem coe_fockEquiv (u : FockAlg) : ((fockEquiv u : lpFiniteModes Conf) : Fock)
    = toLp u := rfl

theorem coe_fockEquiv_symm (x : lpFiniteModes Conf) :
    ((x : lpFiniteModes Conf) : Fock) = toLp (fockEquiv.symm x) := by
  rw [← coe_fockEquiv, LinearEquiv.apply_symm_apply]

theorem creVec_apply (v : ℕ →₀ ℂ) (x : FockAlg) :
    creVec v x = ∑ j ∈ v.support, v j • creA j x := by
  simp [creVec, LinearMap.sum_apply]

@[simp] theorem dGamma_single (col : ℕ → (ℕ →₀ ℂ)) (β : Conf) (c : ℂ) :
    dGamma col (Finsupp.single β c)
      = c • ∑ k ∈ β.support, creVec (col k) (annA k (Finsupp.single β 1)) := by
  simp [dGamma, LinearMap.toSpanSingleton]

theorem sum_creVec_annA_subset (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) {K L : Finset ℕ}
    (hKL : K ⊆ L) (hK : modes u ⊆ K) :
    ∑ k ∈ K, creVec (col k) (annA k u) = ∑ k ∈ L, creVec (col k) (annA k u) :=
  Finset.sum_subset hKL fun k _ hk => by
    rw [annA_eq_zero_of_not_mem_modes (fun hc => hk (hK hc)), map_zero]

theorem dGamma_eq_sum_aux (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) :
    ∀ K : Finset ℕ, modes u ⊆ K → dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => intro K _; simp
  | add f g hf hg =>
    intro K hK
    have hL1 : modes f ⊆ K ∪ (modes f ∪ modes g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_left _ hx)
    have hL2 : modes g ⊆ K ∪ (modes f ∪ modes g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_right _ hx)
    have hKL : K ⊆ K ∪ (modes f ∪ modes g) := Finset.subset_union_left
    rw [map_add, hf _ hL1, hg _ hL2, ← Finset.sum_add_distrib,
      sum_creVec_annA_subset col (f + g) hKL hK]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_add]
  | single β c =>
    intro K hK
    have hsingle : (Finsupp.single β c : FockAlg) = c • Finsupp.single β (1 : ℂ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hc : c = 0
    · subst hc
      simp
    have hb : β.support ⊆ K := by
      refine fun i hi => hK ?_
      exact Finset.mem_biUnion.mpr ⟨β, Finsupp.mem_support_iff.mpr (by simpa using hc), hi⟩
    have hzero : ∀ k ∈ K, k ∉ β.support →
        creVec (col k) (annA k (Finsupp.single β c)) = 0 := by
      intro k _ hk
      have hβ : β k = 0 := by simpa using hk
      have hz : annA k (Finsupp.single β c) = 0 := by
        rw [annA_single, hβ]
        simp
      rw [hz, map_zero]
    rw [← Finset.sum_subset hb hzero, dGamma_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsingle, map_smul, map_smul]

theorem dGamma_eq_sum (col : ℕ → (ℕ →₀ ℂ)) {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) :
    dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u) :=
  dGamma_eq_sum_aux col u K hK

theorem dGamma_one_particle (col : ℕ → (ℕ →₀ ℂ)) (k : ℕ) :
    dGamma col (Finsupp.single (Finsupp.single k 1) 1)
      = ∑ j ∈ (col k).support, (col k) j • Finsupp.single (Finsupp.single j 1) (1 : ℂ) := by
  classical
  have hup : ∀ j : ℕ, up j (0 : Conf) = Finsupp.single j 1 := by
    intro j
    refine Finsupp.ext fun i => ?_
    by_cases h : i = j
    · subst h; simp
    · rw [up_of_ne _ h]
      simp [h]
  have hsupp : (Finsupp.single k 1 : Conf).support = {k} :=
    Finsupp.support_single_ne_zero k one_ne_zero
  have hdn : dn k (Finsupp.single k 1 : Conf) = 0 := by
    refine Finsupp.ext fun i => ?_
    by_cases h : i = k
    · subst h; simp
    · rw [dn_of_ne _ h]
      simp [h]
  rw [dGamma_single, hsupp]
  have hann : annA k (Finsupp.single (Finsupp.single k 1 : Conf) (1 : ℂ))
      = Finsupp.single (0 : Conf) (1 : ℂ) := by
    rw [annA_single, hdn]
    simp
  rw [Finset.sum_singleton, hann, one_smul, creVec_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [creA_single, hup j]
  simp

@[simp] theorem toLp_zero : toLp (0 : FockAlg) = 0 := map_zero toLpL

theorem inner_creVec_annA (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (k : ℕ) {L : Finset ℕ}
    (h : (col k).support ⊆ L) :
    (inner ℂ (toLp (creVec (col k) (annA k u))) (toLp v) : ℂ)
      = ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
          * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hexp : toLp (creVec (col k) (annA k u))
      = ∑ j ∈ (col k).support, (col k) j • toLp (creA j (annA k u)) := by
    rw [creVec_apply, ← toLpL_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, toLpL_apply]
  rw [hexp, sum_inner, ← Finset.sum_subset h (fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, map_zero, zero_mul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_creA_left]

theorem inner_annA_creVec (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (j : ℕ) {L : Finset ℕ}
    (h : (col j).support ⊆ L) :
    (inner ℂ (toLp u) (toLp (creVec (col j) (annA j v))) : ℂ)
      = ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hexp : toLp (creVec (col j) (annA j v))
      = ∑ k ∈ (col j).support, (col j) k • toLp (creA k (annA j v)) := by
    rw [creVec_apply, ← toLpL_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, toLpL_apply]
  rw [hexp, inner_sum, ← Finset.sum_subset h (fun k _ hk => by
    rw [Finsupp.notMem_support_iff.mp hk, zero_mul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, inner_creA_right]

theorem inner_dGamma_left (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) {L : Finset ℕ}
    (hu : modes u ⊆ L)
    (hL : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ L) :
    (inner ℂ (toLp (dGamma col u)) (toLp v) : ℂ)
      = ∑ k ∈ L, ∑ j ∈ L,
        (starRingEnd ℂ) ((col k) j) * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hsum : toLp (dGamma col u) = ∑ k ∈ L, toLp (creVec (col k) (annA k u)) := by
    rw [dGamma_eq_sum col hu, ← toLpL_apply, map_sum]
    rfl
  rw [hsum, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hku : k ∈ modes u
  · exact inner_creVec_annA col u v k (hL k (Finset.mem_union_left _ hku))
  · have h0 : annA k u = 0 := annA_eq_zero_of_not_mem_modes hku
    rw [h0, map_zero]
    simp

theorem inner_dGamma_right (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) {L : Finset ℕ}
    (hv : modes v ⊆ L)
    (hL : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ L) :
    (inner ℂ (toLp u) (toLp (dGamma col v)) : ℂ)
      = ∑ j ∈ L, ∑ k ∈ L,
        (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hsum : toLp (dGamma col v) = ∑ j ∈ L, toLp (creVec (col j) (annA j v)) := by
    rw [dGamma_eq_sum col hv, ← toLpL_apply, map_sum]
    rfl
  rw [hsum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hjv : j ∈ modes v
  · exact inner_annA_creVec col u v j (hL j (Finset.mem_union_right _ hjv))
  · have h0 : annA j v = 0 := annA_eq_zero_of_not_mem_modes hjv
    rw [h0, map_zero]
    simp

theorem modes_left_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    modes u ⊆ closureModes col u v := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem modes_right_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    modes v ⊆ closureModes col u v := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_right _ hx)

theorem col_support_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ closureModes col u v := by
  intro k hk i hi
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk, hi⟩)

theorem inner_dGamma_symm {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) (u v : FockAlg) :
    (inner ℂ (toLp (dGamma col u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (dGamma col v)) := by
  rw [inner_dGamma_left col u v (modes_left_subset_closure col u v)
      (col_support_subset_closure col u v),
    inner_dGamma_right col u v (modes_right_subset_closure col u v)
      (col_support_subset_closure col u v),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hherm j k, Complex.conj_conj]

theorem inner_dGamma_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) (u : FockAlg) :
    0 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by
  classical
  set L := closureModes col u u with hLdef
  set S : Finset Conf := L.biUnion fun k => (annA k u).support with hSdef
  rw [inner_dGamma_right col u u (modes_right_subset_closure col u u)
    (col_support_subset_closure col u u)]
  have hinner : ∀ k ∈ L, ∀ j : ℕ,
      (inner ℂ (toLp (annA k u)) (toLp (annA j u)) : ℂ)
        = ∑ α ∈ S, (starRingEnd ℂ) ((annA k u) α) * (annA j u) α := by
    intro k hk j
    exact inner_toLp_of_subset (fun α hα => Finset.mem_biUnion.mpr ⟨k, hk, hα⟩) _
  have hstep : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j u)))
      = ∑ α ∈ S, ∑ j ∈ L, ∑ k ∈ L,
          (starRingEnd ℂ) ((annA j u) α) * (col k) j * ((annA k u) α) := by
    have h1 : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j u)))
        = ∑ j ∈ L, ∑ k ∈ L, ∑ α ∈ S,
            (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k hk => ?_
      rw [hinner k hk j, Finset.mul_sum]
    rw [h1]
    rw [Finset.sum_comm (s := L) (t := L)]
    rw [show (∑ k ∈ L, ∑ j ∈ L, ∑ α ∈ S,
          (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α))
        = ∑ k ∈ L, ∑ α ∈ S, ∑ j ∈ L,
          (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α) from
      Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm (s := L) (t := S)]
    refine Finset.sum_congr rfl fun α _ => ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hstep, Complex.re_sum]
  refine Finset.sum_nonneg fun α _ => hpos L fun k => (annA k u) α

theorem coe_dGammaOp (col : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) :
    dGammaOp col x = toLp (dGamma col (fockEquiv.symm x)) := by
  simp [dGammaOp, LinearEquiv.conj_apply, coe_fockEquiv]

theorem dGammaOp_symmetricOn {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (lpFiniteModes Conf) (dGammaOp col) := by
  intro x y
  rw [coe_dGammaOp, coe_dGammaOp, coe_fockEquiv_symm x, coe_fockEquiv_symm y]
  exact inner_dGamma_symm hherm _ _

theorem dGammaOp_quadForm_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : lpFiniteModes Conf) : 0 ≤ quadForm (dGammaOp col) x := by
  rw [quadForm, coe_dGammaOp, coe_fockEquiv_symm x]
  exact inner_dGamma_nonneg hpos _

theorem finiteOccupation_dense : Dense ((lpFiniteModes Conf : Submodule ℂ Fock) : Set Fock) :=
  lpFiniteModes_dense

theorem dGammaOpB_symmetricOn {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (finiteModeDomain (fockBasisN ε)) (dGammaOpB ε col) := by
  intro x y
  exact dGammaOp_symmetricOn hherm
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) x)
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) y)

theorem dGammaOpB_quadForm_nonneg {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : finiteModeDomain (fockBasisN ε)) : 0 ≤ quadForm (dGammaOpB ε col) x :=
  dGammaOp_quadForm_nonneg hpos
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) x)
end
end BookProof.FockSecondQuantization

open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert
theorem solution {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (lpFiniteModes Conf) (dGammaOp col) := by
  exact BookProof.FockSecondQuantization.dGammaOp_symmetricOn hherm
#print axioms solution
