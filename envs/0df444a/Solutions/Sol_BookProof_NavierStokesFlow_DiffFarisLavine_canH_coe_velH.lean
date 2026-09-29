-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.canH_coe_velH
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:00:01.222244+00:00
-- url     : https://prove2.me/submissions/d46ba062-7327-4cc5-b2b3-73b023f9ddae

/- Source adaptation: Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesCanonicalVector.lean -/
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Mathlib
set_option maxHeartbeats 4000000
noncomputable section
open scoped ENNReal
namespace BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
variable {ι : Type*} {sym : ι → ℝ}
namespace SignedHop
variable (S : SignedHop ι sym)
@[simp] theorem hopH_coe (x : maxDom sym) (β : ι) :
    ((hopH S x : L2I ι) : ι → ℂ) β = S.hFun ((x : L2I ι) : ι → ℂ) β := rfl

end SignedHop
@[simp] theorem listH_cons (S : SignedHop ι sym) (L : List (SignedHop ι sym)) :
    listH (S :: L) = SignedHop.hopH S + listH L := rfl

theorem listH_coe {sym : ι → ℝ} (L : List (SignedHop ι sym)) (x : maxDom sym) (γ : ι) :
    ((listH L x : L2I ι) : ι → ℂ) γ
      = (L.map (fun S => S.hFun ((x : L2I ι) : ι → ℂ) γ)).sum := by
  induction L with
  | nil => simp [listH]
  | cons S L ih =>
      rw [listH_cons]
      simp only [LinearMap.add_apply, lp.coeFn_add, Pi.add_apply, List.map_cons,
        List.sum_cons, SignedHop.hopH_coe, ih]

end BookProof.NavierStokesFlow.SignedShift
namespace BookProof.NavierStokesFlow.ThreeComponent
open LpNat FarisLavine IkebeKato ShiftHamiltonian SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem hopList_eq : hopList A c =
    [diagHop A c 0, shearHop A c 0,
      pairHop A c 0 0, rotHop A c 0 0, pairHop A c 0 1, rotHop A c 0 1,
      pairHop A c 0 2, rotHop A c 0 2,
     diagHop A c 1, shearHop A c 1,
      pairHop A c 1 0, rotHop A c 1 0, pairHop A c 1 1, rotHop A c 1 1,
      pairHop A c 1 2, rotHop A c 1 2,
     diagHop A c 2, shearHop A c 2,
      pairHop A c 2 0, rotHop A c 2 0, pairHop A c 2 1, rotHop A c 2 1,
      pairHop A c 2 2, rotHop A c 2 2] := rfl

@[simp] theorem diagHop_shift (i : Fin 3) : (diagHop A c i).shift = shDiag i := rfl

@[simp] theorem diagHop_amp (i : Fin 3) : (diagHop A c i).amp = ampDiag A i := rfl

@[simp] theorem shearHop_shift (i : Fin 3) : (shearHop A c i).shift = shShear i := rfl

@[simp] theorem shearHop_amp (i : Fin 3) : (shearHop A c i).amp = ampShear c i := rfl

@[simp] theorem pairHop_shift (i k : Fin 3) : (pairHop A c i k).shift = shPair i k := rfl

@[simp] theorem pairHop_amp (i k : Fin 3) : (pairHop A c i k).amp = ampPair A i k := rfl

@[simp] theorem rotHop_shift (i k : Fin 3) : (rotHop A c i k).shift = shRot i k := rfl

@[simp] theorem rotHop_amp (i k : Fin 3) : (rotHop A c i k).amp = ampRot A i k := rfl

end BookProof.NavierStokesFlow.ThreeComponent
namespace BookProof.NavierStokesFlow.CanonicalVector
open LpNat FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift
theorem raise_comm (i k : Fin 3) (β : Vel) : raise i (raise k β) = raise k (raise i β) := by
  funext j
  by_cases hji : j = i <;> by_cases hjk : j = k
  · subst hji; subst hjk; simp [raise]
  · subst hji; rw [raise_self, raise_of_ne hjk, raise_of_ne hjk, raise_self]
  · subst hjk; rw [raise_of_ne hji, raise_self, raise_self, raise_of_ne hji]
  · rw [raise_of_ne hji, raise_of_ne hjk, raise_of_ne hjk, raise_of_ne hji]

theorem lower_comm (i k : Fin 3) (β : Vel) : lower i (lower k β) = lower k (lower i β) := by
  funext j
  by_cases hji : j = i <;> by_cases hjk : j = k
  · subst hji; subst hjk; simp [lower]
  · subst hji; rw [lower_self, lower_of_ne hjk, lower_of_ne hjk, lower_self]
  · subst hjk; rw [lower_of_ne hji, lower_self, lower_self, lower_of_ne hji]
  · rw [lower_of_ne hji, lower_of_ne hjk, lower_of_ne hjk, lower_of_ne hji]

@[simp] theorem lower_raise (i : Fin 3) (β : Vel) : lower i (raise i β) = β := by
  funext j
  by_cases hji : j = i
  · subst hji; rw [lower_self, raise_self]; omega
  · rw [lower_of_ne hji, raise_of_ne hji]

theorem lower_raise_of_ne {i k : Fin 3} (h : i ≠ k) (β : Vel) :
    lower k (raise i β) = raise i (lower k β) := by
  funext j
  by_cases hji : j = i <;> by_cases hjk : j = k
  · exact absurd (hji ▸ hjk ▸ rfl) h
  · subst hji; rw [lower_of_ne hjk, raise_self, raise_self, lower_of_ne hjk]
  · subst hjk; rw [lower_self, raise_of_ne hji, raise_of_ne hji, lower_self]
  · rw [lower_of_ne hjk, raise_of_ne hji, raise_of_ne hji, lower_of_ne hjk]

@[simp] theorem crd_ann (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (ann i x) = aFun i (crd x) := rfl

@[simp] theorem crd_cre (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (cre i x) = cFun i (crd x) := rfl

@[simp] theorem crd_add (x y : lpFiniteModes Vel) : crd (x + y) = crd x + crd y := by
  funext β; simp [crd]

@[simp] theorem crd_smul (a : ℂ) (x : lpFiniteModes Vel) : crd (a • x) = a • crd x := by
  funext β; simp [crd]

@[simp] theorem crd_sub (x y : lpFiniteModes Vel) : crd (x - y) = crd x - crd y := by
  funext β; simp [crd]

theorem crd_injective : Function.Injective crd := by
  intro x y h
  exact Subtype.ext (lp.ext h)

@[simp] theorem aFun_add (i : Fin 3) (X Y : Vel → ℂ) :
    aFun i (X + Y) = aFun i X + aFun i Y := by
  funext β; simp [aFun]; ring

@[simp] theorem aFun_sub (i : Fin 3) (X Y : Vel → ℂ) :
    aFun i (X - Y) = aFun i X - aFun i Y := by
  funext β; simp [aFun]; ring

@[simp] theorem aFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) :
    aFun i (a • X) = a • aFun i X := by
  funext β; simp [aFun]; ring

@[simp] theorem cFun_add (i : Fin 3) (X Y : Vel → ℂ) :
    cFun i (X + Y) = cFun i X + cFun i Y := by
  funext β; simp [cFun]; ring

@[simp] theorem cFun_sub (i : Fin 3) (X Y : Vel → ℂ) :
    cFun i (X - Y) = cFun i X - cFun i Y := by
  funext β; simp [cFun]; ring

@[simp] theorem cFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) :
    cFun i (a • X) = a • cFun i X := by
  funext β; simp [cFun]; ring

theorem aFun_comm (i k : Fin 3) (X : Vel → ℂ) : aFun i (aFun k X) = aFun k (aFun i X) := by
  by_cases hik : i = k
  · rw [hik]
  · funext β
    simp only [aFun, raise_of_ne (Ne.symm hik), raise_of_ne hik, raise_comm i k β]
    ring

theorem cFun_comm (i k : Fin 3) (X : Vel → ℂ) : cFun i (cFun k X) = cFun k (cFun i X) := by
  by_cases hik : i = k
  · rw [hik]
  · funext β
    simp only [cFun, lower_of_ne (Ne.symm hik), lower_of_ne hik, lower_comm i k β]
    ring

theorem aFun_cFun_of_ne {i k : Fin 3} (h : i ≠ k) (X : Vel → ℂ) :
    aFun i (cFun k X) = cFun k (aFun i X) := by
  funext β
  simp only [aFun, cFun, raise_of_ne (Ne.symm h), lower_of_ne h,
    lower_raise_of_ne h β]
  ring

theorem inv_sqrt_two_sq : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)
    = ((1 / 2 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem hFun_eq_of_incoming {sym : Vel → ℝ} (S : SignedHop Vel sym) (X g : Vel → ℂ)
    (h1 : ∀ β, g (S.shift β) = (S.amp β : ℂ) * X β)
    (h2 : ∀ γ, (¬ ∃ α, S.shift α = γ) → g γ = 0) (γ : Vel) :
    S.hFun X γ = Complex.I * (g γ - (S.amp γ : ℂ) * X (S.shift γ)) := by
  have hkey : S.maj.hop (fun α => (S.amp α : ℂ) * X α) γ = g γ := by
    by_cases hb : ∃ α, S.shift α = γ
    · obtain ⟨α, rfl⟩ := hb
      have hs : S.maj.hop (fun α => (S.amp α : ℂ) * X α) (S.maj.shift α)
          = (S.amp α : ℂ) * X α := ShiftData.hop_shift _ _ _
      exact hs.trans (h1 α).symm
    · rw [ShiftData.hop_eq_zero _ _ hb, h2 γ hb]
  rw [SignedHop.hFun, hkey]

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem diagHop_hFun (i : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (diagHop A c i).hFun X γ
      = Complex.I * (((A i i / 2 : ℝ) : ℂ) * (cFun i (cFun i X) γ - aFun i (aFun i X) γ)) := by
  have key := hFun_eq_of_incoming (diagHop A c i) X
    (fun δ => ((A i i / 2 : ℝ) : ℂ) * cFun i (cFun i X) δ) ?_ ?_ γ
  · rw [key]
    congr 1
    have hout : ((diagHop A c i).amp γ : ℂ) * X ((diagHop A c i).shift γ)
        = ((A i i / 2 : ℝ) : ℂ) * aFun i (aFun i X) γ := by
      simp only [diagHop_amp, diagHop_shift, ampDiag, aFun, shDiag, raise_self]
      rw [Real.sqrt_mul (by positivity)]
      push_cast
      ring_nf
    rw [hout]
    ring
  · intro β
    simp only [diagHop_amp, diagHop_shift, ampDiag, cFun, shDiag, raise_self, lower_raise]
    rw [Real.sqrt_mul (by positivity)]
    push_cast
    ring_nf
  · intro δ hno
    have hlt : δ i < 2 := by
      by_contra hcon
      exact hno ⟨lower i (lower i δ), by
        have h1 : 1 ≤ (lower i δ) i := by simp only [lower_self]; omega
        simp only [diagHop_shift, shDiag]
        rw [raise_lower i h1, raise_lower i (by omega : 1 ≤ δ i)]⟩
    interval_cases h : δ i <;> simp [cFun, h, lower_self]

theorem pairHop_hFun (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (pairHop A c i k).hFun X γ
      = Complex.I * (((coefPair A i k : ℝ) : ℂ)
        * (cFun i (cFun k X) γ - aFun i (aFun k X) γ)) := by
  by_cases hik : i = k
  · subst hik
    have hz : coefPair A i i = 0 := by simp [coefPair]
    have hamp : ∀ β, ampPair A i i β = 0 := by intro β; simp [ampPair, hz]
    have key := hFun_eq_of_incoming (pairHop A c i i) X (fun _ => 0)
      (by intro β; simp only [pairHop_amp, hamp]; simp)
      (by intro δ _; rfl) γ
    rw [key, hz]
    simp [pairHop_amp, hamp]
  · have key := hFun_eq_of_incoming (pairHop A c i k) X
      (fun δ => ((coefPair A i k : ℝ) : ℂ) * cFun i (cFun k X) δ) ?_ ?_ γ
    · rw [key]
      congr 1
      have hout : ((pairHop A c i k).amp γ : ℂ) * X ((pairHop A c i k).shift γ)
          = ((coefPair A i k : ℝ) : ℂ) * aFun i (aFun k X) γ := by
        simp only [pairHop_amp, pairHop_shift, ampPair, aFun, shPair,
          raise_of_ne (Ne.symm hik), raise_comm k i γ]
        rw [Real.sqrt_mul (by positivity)]
        push_cast
        ring
      rw [hout]
      ring
    · intro β
      simp only [pairHop_amp, pairHop_shift, ampPair, cFun, shPair, raise_self,
        raise_of_ne hik, lower_raise]
      rw [Real.sqrt_mul (by positivity)]
      push_cast
      ring
    · intro δ hno
      have hz : δ i = 0 ∨ δ k = 0 := by
        by_contra hcon
        push_neg at hcon
        refine hno ⟨lower k (lower i δ), ?_⟩
        have hik1 : 1 ≤ δ i := Nat.one_le_iff_ne_zero.mpr hcon.1
        have hkk1 : 1 ≤ δ k := Nat.one_le_iff_ne_zero.mpr hcon.2
        have h1 : 1 ≤ (lower i δ) k := by
          rw [lower_of_ne (Ne.symm hik)]; omega
        simp only [pairHop_shift, shPair]
        rw [raise_lower k h1, raise_lower i hik1]
      rcases hz with h0 | h0
      · simp [cFun, h0]
      · simp [cFun, lower_of_ne (Ne.symm hik), h0]

theorem rotHop_hFun (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (rotHop A c i k).hFun X γ
      = Complex.I * (((coefRot A i k : ℝ) : ℂ)
        * (cFun i (aFun k X) γ - aFun i (cFun k X) γ)) := by
  by_cases hik : i = k
  · subst hik
    have hz : coefRot A i i = 0 := by simp [coefRot]
    have hamp : ∀ β, ampRot A i i β = 0 := by intro β; simp [ampRot, hz]
    have key := hFun_eq_of_incoming (rotHop A c i i) X (fun _ => 0)
      (by intro β; simp only [rotHop_amp, hamp]; simp)
      (by intro δ _; rfl) γ
    rw [key, hz]
    simp [rotHop_amp, hamp]
  · have key := hFun_eq_of_incoming (rotHop A c i k) X
      (fun δ => ((coefRot A i k : ℝ) : ℂ) * cFun i (aFun k X) δ) ?_ ?_ γ
    · rw [key]
      congr 1
      have hout : ((rotHop A c i k).amp γ : ℂ) * X ((rotHop A c i k).shift γ)
          = ((coefRot A i k : ℝ) : ℂ) * aFun i (cFun k X) γ := by
        rcases Nat.eq_zero_or_pos (γ k) with h0 | hpos
        · simp [rotHop_amp, ampRot, aFun, cFun, raise_of_ne (Ne.symm hik), h0]
        · have hne : γ k ≠ 0 := by omega
          simp only [rotHop_amp, rotHop_shift, ampRot, aFun, cFun, shRot, if_neg hne,
            raise_of_ne (Ne.symm hik), lower_raise_of_ne hik]
          rw [Real.sqrt_mul (by positivity)]
          push_cast
          ring
      rw [hout]
      ring
    · intro β
      rcases Nat.eq_zero_or_pos (β k) with h0 | hpos
      · have hswap : (swapVel i k β) i = 0 := by
          rw [swapVel_apply, Equiv.swap_apply_left]; exact h0
        have hL : cFun i (aFun k X) (shRot i k β) = 0 := by
          simp only [shRot, if_pos h0, cFun, hswap]
          simp
        have hR : ampRot A i k β = 0 := by
          simp only [ampRot, h0]
          simp
        simp only [rotHop_amp, rotHop_shift]
        rw [hL, hR]
        simp
      · have hne : β k ≠ 0 := by omega
        have hcast : (((β k - 1 : ℕ) : ℝ) + 1) = ((β k : ℝ)) := by
          have h1 : (1 : ℕ) ≤ β k := hpos
          push_cast [Nat.cast_sub h1]
          ring
        simp only [rotHop_amp, rotHop_shift, ampRot, cFun, aFun, shRot, if_neg hne,
          raise_self, lower_raise, lower_of_ne hik, lower_self, hcast,
          raise_lower k hpos]
        rw [Real.sqrt_mul (by positivity)]
        push_cast
        ring
    · intro δ hno
      have hz : δ i = 0 := by
        by_contra hcon
        have hik1 : 1 ≤ δ i := Nat.one_le_iff_ne_zero.mpr hcon
        refine hno ⟨raise k (lower i δ), ?_⟩
        have hk : (raise k (lower i δ)) k ≠ 0 := by rw [raise_self]; omega
        simp only [rotHop_shift, shRot, if_neg hk]
        rw [lower_raise, raise_lower i hik1]
      simp [cFun, hz]

theorem shearHop_hFun (i : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (shearHop A c i).hFun X γ
      = Complex.I * (((c i / Real.sqrt 2 : ℝ) : ℂ) * (cFun i X γ - aFun i X γ)) := by
  have key := hFun_eq_of_incoming (shearHop A c i) X
    (fun δ => ((c i / Real.sqrt 2 : ℝ) : ℂ) * cFun i X δ) ?_ ?_ γ
  · rw [key]
    congr 1
    have hout : ((shearHop A c i).amp γ : ℂ) * X ((shearHop A c i).shift γ)
        = ((c i / Real.sqrt 2 : ℝ) : ℂ) * aFun i X γ := by
      simp only [shearHop_amp, shearHop_shift, ampShear, aFun, shShear]
      push_cast
      ring
    rw [hout]
    ring
  · intro β
    simp only [shearHop_amp, shearHop_shift, ampShear, cFun, shShear, raise_self, lower_raise]
    push_cast
    ring
  · intro δ hno
    have hz : δ i = 0 := by
      by_contra hcon
      exact hno ⟨lower i δ, by
        simp only [shearHop_shift, shShear]
        exact raise_lower i (Nat.one_le_iff_ne_zero.mpr hcon)⟩
    simp [cFun, hz]

@[simp] theorem coe_inclusion_finiteModes (sym : Vel → ℝ) (x : lpFiniteModes Vel) :
    ((Submodule.inclusion (finiteModes_le_maxDom sym) x : maxDom sym) : L2I Vel)
      = (x : L2I Vel) := rfl

theorem velH_crd (x : lpFiniteModes Vel) (γ : Vel) :
    ((velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x) :
        L2I Vel) : Vel → ℂ) γ
      = ladFun A c (crd x) γ := by
  rw [velH, SignedShift.listH_coe]
  simp only [hopList_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    diagHop_hFun, shearHop_hFun, pairHop_hFun, rotHop_hFun, ladFun, Fin.sum_univ_three,
    coe_inclusion_finiteModes, crd]
  push_cast
  ring

@[simp] theorem pFun_add (i : Fin 3) (X Y : Vel → ℂ) :
    pFun i (X + Y) = pFun i X + pFun i Y := by
  funext δ; simp only [pFun, cFun_add, aFun_add, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]; ring

@[simp] theorem pFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) :
    pFun i (a • X) = a • pFun i X := by
  funext δ; simp only [pFun, cFun_smul, aFun_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]; ring

@[simp] theorem crd_pos (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (pos i x) = pFun i (crd x) := by
  simp only [pos, pFun, LinearMap.smul_apply, LinearMap.add_apply, crd_smul, crd_add,
    crd_cre, crd_ann]

@[simp] theorem crd_mom (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (mom i x) = mFun i (crd x) := by
  simp only [mom, mFun, LinearMap.smul_apply, LinearMap.sub_apply, crd_smul, crd_sub,
    crd_cre, crd_ann]

theorem crd_fieldV (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (fieldV A c i x) = vFun A c i (crd x) := by
  funext γ
  simp only [fieldV, vFun, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Fin.sum_univ_three, crd_add, crd_smul, crd_pos, Pi.add_apply, Pi.smul_apply]

theorem canH_crd (x : lpFiniteModes Vel) (γ : Vel) :
    crd (canH A c x) γ = canFun A c (crd x) γ := by
  simp only [canH, canFun, Fin.sum_univ_three, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, crd_smul, crd_add, crd_mom, crd_fieldV,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

@[simp] theorem mFun_add (i : Fin 3) (X Y : Vel → ℂ) :
    mFun i (X + Y) = mFun i X + mFun i Y := by
  funext δ; simp only [mFun, cFun_add, aFun_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]; ring

@[simp] theorem mFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) :
    mFun i (a • X) = a • mFun i X := by
  funext δ; simp only [mFun, cFun_smul, aFun_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]; ring

theorem symProdFun_eq (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    symProdFun i k X γ
      = (Complex.I / 4) * (cFun i (cFun k X) γ + cFun i (aFun k X) γ
          - aFun i (cFun k X) γ - aFun i (aFun k X) γ
          + cFun k (cFun i X) γ - cFun k (aFun i X) γ
          + aFun k (cFun i X) γ - aFun k (aFun i X) γ) := by
  have hs2 : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
    rw [inv_sqrt_two_sq]; norm_num
  simp only [symProdFun, mFun, pFun, cFun_add, aFun_add, cFun_sub, aFun_sub, cFun_smul,
    aFun_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (Complex.I / 2 * (cFun i (cFun k X) γ + cFun i (aFun k X) γ
      - aFun i (cFun k X) γ - aFun i (aFun k X) γ
      + cFun k (cFun i X) γ - cFun k (aFun i X) γ
      + aFun k (cFun i X) γ - aFun k (aFun i X) γ)) * hs2

theorem canFun_eq_sum (X : Vel → ℂ) (γ : Vel) :
    canFun A c X γ
      = ∑ i, ((∑ k, ((A i k : ℝ) : ℂ) * symProdFun i k X γ) + ((c i : ℝ) : ℂ) * mFun i X γ) := by
  simp only [canFun, vFun, symProdFun, Fin.sum_univ_three, mFun_add, mFun_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem canFun_eq_ladFun (X : Vel → ℂ) (γ : Vel) :
    canFun A c X γ = ladFun A c X γ := by
  rw [canFun_eq_sum]
  simp +decide only [ladFun, mFun, symProdFun_eq, Fin.sum_univ_three,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, coefPair, coefRot,
    aFun_cFun_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    aFun_cFun_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    aFun_cFun_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    aFun_cFun_of_ne (show (1 : Fin 3) ≠ 2 by decide),
    aFun_cFun_of_ne (show (2 : Fin 3) ≠ 0 by decide),
    aFun_cFun_of_ne (show (2 : Fin 3) ≠ 1 by decide),
    cFun_comm 1 0, cFun_comm 2 0, cFun_comm 2 1,
    aFun_comm 1 0, aFun_comm 2 0, aFun_comm 2 1]
  push_cast
  ring

theorem canH_eq_velH :
    (lpFiniteModes Vel).subtype.comp (canH A c)
      = (velH A c).comp (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c)))) := by
  refine LinearMap.ext fun x => lp.ext (funext fun γ => ?_)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [velH_crd]
  exact (canH_crd A c x γ).trans (canFun_eq_ladFun A c (crd x) γ)

end BookProof.NavierStokesFlow.CanonicalVector
namespace BookProof.NavierStokesFlow.DiffFarisLavine
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem canH_coe_velH (x : lpFiniteModes Vel) :
    ((canH A c x : lpFiniteModes Vel) : L2I Vel)
      = velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x) := by
  have h := congrFun (congrArg (fun T : lpFiniteModes Vel →ₗ[ℂ] L2I Vel => ⇑T)
    (canH_eq_velH A c)) x
  simpa using h

end BookProof.NavierStokesFlow.DiffFarisLavine

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.canH_coe_velH
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiffFarisLavine













open MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2


















variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem solution (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (x : lpFiniteModes Vel) :
    ((canH A c x : lpFiniteModes Vel) : L2I Vel)
      = velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x) := by
  exact BookProof.NavierStokesFlow.DiffFarisLavine.canH_coe_velH A c x
#print axioms solution
example : (∀ (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (x : lpFiniteModes Vel) , 
    ((canH A c x : lpFiniteModes Vel) : L2I Vel)
      = velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x)) := @solution
