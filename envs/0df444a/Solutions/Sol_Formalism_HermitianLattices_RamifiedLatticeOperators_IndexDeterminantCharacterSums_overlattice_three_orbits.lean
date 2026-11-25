-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.overlattice_three_orbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:03:16.529739+00:00
-- url     : https://prove2.me/submissions/6235b1fe-e37d-418f-9518-c8978625ee07

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
theorem _root_.solution : Formalism.HermitianLattices.RamifiedLatticeOperators.OverlatticeThreeOrbits := by
  intro q hqF n La hz hint
  dsimp only
  have hq2 : 2 ≤ q := hqF.out.two_le
  have : NeZero q := ⟨hqF.out.ne_zero⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqF.out.ne_zero
  have notint : ∀ k : ℤ, (q : ℚ)⁻¹ ≠ k := by
    intro k h
    have h1 : (((q : ℤ) * k : ℤ) : ℚ) = 1 := by
      push_cast; rw [← h, mul_inv_cancel₀ hq0]
    have h2 : (q : ℤ) * k = 1 := by exact_mod_cast h1
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with h3 | h3 <;> omega
  have h10 : (1 : ZMod q) ≠ 0 := one_ne_zero
  have hzm : ∀ m : ℤ, ((0 : Fin n → ℚ), (m : ℚ)) ∈ La := by
    intro m
    have e : ((0 : Fin n → ℚ), (m : ℚ)) = m • ((0 : Fin n → ℚ), (1 : ℚ)) :=
      Prod.ext (by simp) (by simp)
    rw [e]; exact La.zsmul_mem hz m
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hzq : ((0 : Fin n → ℚ), (q : ℚ)⁻¹) ∈ La
    · right; left
      refine ⟨hzq, fun p hp => ?_⟩
      obtain ⟨k, hk⟩ := hint p hp
      have e : (p.1, (0 : ℚ)) = p - k • ((0 : Fin n → ℚ), (q : ℚ)⁻¹) := by
        refine Prod.ext (by simp) ?_
        rw [Prod.snd_sub, Prod.smul_snd, zsmul_eq_mul]
        rw [← hk, mul_comm (q : ℚ) p.2, mul_assoc, mul_inv_cancel₀ hq0, mul_one, sub_self]
      rw [e]; exact La.sub_mem hp (La.zsmul_mem hzq k)
    · have S0 : ∀ s : ℚ, ((0 : Fin n → ℚ), s) ∈ La → ∃ m : ℤ, s = m := by
        intro s hs
        obtain ⟨k, hk⟩ := hint _ hs
        change (q : ℚ) * s = k at hk
        by_cases hk0 : (k : ZMod q) = 0
        · obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k q).mp hk0
          refine ⟨m, ?_⟩
          have h3 : (q : ℚ) * s = q * m := by rw [hk, hm]; push_cast; ring
          exact mul_left_cancel₀ hq0 h3
        · exfalso; apply hzq
          obtain ⟨a, ha⟩ : ∃ a : ZMod q, a * k = 1 := ⟨(k : ZMod q)⁻¹, inv_mul_cancel₀ hk0⟩
          have hd : (((a.val : ℤ) * k - 1 : ℤ) : ZMod q) = 0 := by
            push_cast; rw [ZMod.natCast_zmod_val, ha, sub_self]
          obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hd
          have hb' : ((a.val : ℚ)) * k - 1 = q * b := by exact_mod_cast hb
          have key : (q : ℚ) * ((a.val : ℚ) * s - b) = 1 := by
            linear_combination (a.val : ℚ) * hk + hb'
          have e : ((0 : Fin n → ℚ), (q : ℚ)⁻¹) =
              ((a.val : ℤ) • ((0 : Fin n → ℚ), s) - b • ((0 : Fin n → ℚ), (1 : ℚ))) := by
            refine Prod.ext (by simp) ?_
            rw [Prod.snd_sub, Prod.smul_snd, Prod.smul_snd, zsmul_eq_mul, zsmul_eq_mul, mul_one]
            push_cast
            exact (eq_inv_of_mul_eq_one_right key).symm
          rw [e]; exact La.sub_mem (La.zsmul_mem hs _) (La.zsmul_mem hz b)
      have hmem : ∀ a : La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ), ∃ s : ℚ, (a.1, s) ∈ La := by
        rintro ⟨a, ha⟩
        obtain ⟨p, hp, rfl⟩ := AddSubgroup.mem_map.mp ha
        exact ⟨p.2, by simpa using hp⟩
      choose sel hsel using hmem
      have hfloor : ∀ a, (q : ℚ) * sel a = ((⌊(q : ℚ) * sel a⌋ : ℤ) : ℚ) := by
        intro a; obtain ⟨k, hk⟩ := hint _ (hsel a)
        change (q : ℚ) * sel a = k at hk
        rw [hk, Int.floor_intCast]
      let fv : La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ) → ZMod q :=
        fun a => ((⌊(q : ℚ) * sel a⌋ : ℤ) : ZMod q)
      have W : ∀ p ∈ La, ∀ a : La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ), p.1 = a.1 →
          ∀ k : ℤ, (q : ℚ) * p.2 = k → (k : ZMod q) = fv a := by
        intro p hp a hpa k hk
        have hd : ((0 : Fin n → ℚ), p.2 - sel a) ∈ La := by
          have e : ((0 : Fin n → ℚ), p.2 - sel a) = p - (a.1, sel a) :=
            Prod.ext (by simp [hpa]) (by simp)
          rw [e]; exact La.sub_mem hp (hsel a)
        obtain ⟨m, hm⟩ := S0 _ hd
        have h1 : ((⌊(q : ℚ) * sel a⌋ : ℤ) : ℚ) = ((k - q * m : ℤ) : ℚ) := by
          rw [← hfloor]; push_cast
          linear_combination (-(q : ℚ)) * hm + hk
        have h2 : (⌊(q : ℚ) * sel a⌋ : ℤ) = k - q * m := by exact_mod_cast h1
        show (k : ZMod q) = ((⌊(q : ℚ) * sel a⌋ : ℤ) : ZMod q)
        rw [h2]; push_cast; simp [ZMod.natCast_self]
      have fv_zero : fv 0 = 0 := by
        have h := W 0 La.zero_mem 0 rfl 0 (by simp)
        simpa using h.symm
      have fv_add : ∀ a b, fv (a + b) = fv a + fv b := by
        intro a b
        have h := W ((a.1, sel a) + (b.1, sel b)) (La.add_mem (hsel a) (hsel b)) (a + b) (by simp)
          (⌊(q : ℚ) * sel a⌋ + ⌊(q : ℚ) * sel b⌋)
          (by rw [Int.cast_add, ← hfloor, ← hfloor, Prod.snd_add, mul_add])
        rw [← h]; push_cast; rfl
      let f : La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ) →+ ZMod q :=
        { toFun := fv, map_zero' := fv_zero, map_add' := fv_add }
      have C : ∀ p : (Fin n → ℚ) × ℚ, p ∈ La ↔
          ∃ h : p.1 ∈ La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ), ∃ k : ℤ, (q : ℚ) * p.2 = k ∧
            (k : ZMod q) = f ⟨p.1, h⟩ := by
        intro p
        constructor
        · intro hp
          refine ⟨AddSubgroup.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
          obtain ⟨k, hk⟩ := hint p hp
          exact ⟨k, hk, W p hp _ rfl k hk⟩
        · rintro ⟨h, k, hk, hkf⟩
          have hkf' : (k : ZMod q) = ((⌊(q : ℚ) * sel ⟨p.1, h⟩⌋ : ℤ) : ZMod q) := hkf
          have hd : ((k - ⌊(q : ℚ) * sel ⟨p.1, h⟩⌋ : ℤ) : ZMod q) = 0 := by
            push_cast; rw [hkf', sub_self]
          obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hd
          have e2 : p.2 = sel ⟨p.1, h⟩ + m := by
            have h1 : (((k - ⌊(q : ℚ) * sel ⟨p.1, h⟩⌋ : ℤ)) : ℚ) = ((q * m : ℤ) : ℚ) := by rw [hm]
            push_cast at h1
            rw [← hk, ← hfloor] at h1
            have h3 : (q : ℚ) * p.2 = q * (sel ⟨p.1, h⟩ + m) := by linear_combination h1
            exact mul_left_cancel₀ hq0 h3
          have e : p = (p.1, sel ⟨p.1, h⟩) + ((0 : Fin n → ℚ), (m : ℚ)) :=
            Prod.ext (by simp) (by simp [e2])
          rw [e]; exact La.add_mem (hsel ⟨p.1, h⟩) (hzm m)
      by_cases hs : Function.Surjective f
      · right; right
        refine ⟨f, ⟨hs, C⟩, ?_⟩
        rintro f' ⟨_, C'⟩
        ext a
        obtain ⟨h', k', hk', hkf'⟩ := (C' (a.1, sel a)).mp (hsel a)
        obtain ⟨h, k, hk, hkf⟩ := (C (a.1, sel a)).mp (hsel a)
        have hkk : k = k' := by exact_mod_cast hk.symm.trans hk'
        have e1 : f' a = (k' : ZMod q) := hkf'.symm
        have e2 : f a = (k : ZMod q) := hkf.symm
        rw [e1, e2, hkk]
      · left
        have hf0 : ∀ a, f a = 0 := by
          intro a
          by_contra hne
          apply hs
          intro d
          refine ⟨((d * (f a)⁻¹).val) • a, ?_⟩
          rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hne,
            mul_one]
        intro p hp
        obtain ⟨h, k, hk, hkf⟩ := (C p).mp hp
        rw [hf0] at hkf
        obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hkf
        have e2 : p.2 = m := by
          have h3 : (q : ℚ) * p.2 = q * m := by rw [hk, hm]; push_cast; ring
          exact mul_left_cancel₀ hq0 h3
        refine ⟨?_, m, e2⟩
        have e : (p.1, (0 : ℚ)) = p - ((0 : Fin n → ℚ), (m : ℚ)) :=
          Prod.ext (by simp) (by simp [e2])
        rw [e]; exact La.sub_mem hp (hzm m)
  · rintro ⟨h1, h2, _⟩
    obtain ⟨_, k, hk⟩ := h1 _ h2
    exact notint k hk
  · rintro ⟨h1, f, ⟨hs, hC⟩, _⟩
    obtain ⟨a, ha⟩ := hs 1
    have hmem : (a.1, (q : ℚ)⁻¹) ∈ La := (hC _).mpr ⟨a.2, 1,
      by show (q : ℚ) * (q : ℚ)⁻¹ = ((1 : ℤ) : ℚ); rw [mul_inv_cancel₀ hq0, Int.cast_one],
      by show ((1 : ℤ) : ZMod q) = f a; rw [ha, Int.cast_one]⟩
    obtain ⟨_, k, hk⟩ := h1 _ hmem
    exact notint k hk
  · rintro ⟨⟨hzq, _⟩, f, ⟨_, hC⟩, _⟩
    obtain ⟨h, k, hk, hkf⟩ := (hC _).mp hzq
    have hk1 : k = 1 := by
      have h3 : ((k : ℤ) : ℚ) = 1 := by rw [← hk]; exact mul_inv_cancel₀ hq0
      exact_mod_cast h3
    have h4 : f ⟨((0 : Fin n → ℚ), (q : ℚ)⁻¹).1, h⟩ = 0 := by
      have e : (⟨((0 : Fin n → ℚ), (q : ℚ)⁻¹).1, h⟩ : La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ)) = 0 :=
        rfl
      rw [e, map_zero]
    rw [h4, hk1, Int.cast_one] at hkf
    exact h10 hkf
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
