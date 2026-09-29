-- Prove2me | solution 1 for CongruenceSubgroup.natCard_doubleCoset_gamma1_map_T_mul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/302bf6b9-32e1-5ae6-97b4-ebd91f9b262a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_mul_of_coprime

set_option autoImplicit false

open scoped MatrixGroups

namespace CuspKit

theorem map_apply (N : ℕ) (γ : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N)) γ) i j = ((γ i j : ℤ) : ZMod N) := by
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem mem_map_gamma1_iff (N : ℕ) [NeZero N] (g : SL(2, ZMod N)) :
    g ∈ (CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) ↔
      g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1 := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [SetLike.mem_coe, CongruenceSubgroup.Gamma1_mem] at hγ
    obtain ⟨h00, h11, h10⟩ := hγ
    refine ⟨?_, ?_, ?_⟩ <;> rw [map_apply]
    · exact h00
    · exact h10
    · exact h11
  · rintro ⟨h00, h10, h11⟩
    refine ⟨ModularGroup.T ^ ((g 0 1).val : ℤ), ?_, ?_⟩
    · rw [SetLike.mem_coe, CongruenceSubgroup.Gamma1_mem]
      simp [ModularGroup.coe_T_zpow]
    · ext i j
      rw [map_apply]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h00, h10, h11, ZMod.natCast_zmod_val]

theorem mem_map_zpowers_T_iff (N : ℕ) [NeZero N] (g : SL(2, ZMod N)) :
    g ∈ (Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) ↔
      g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1 := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hγ
    obtain ⟨n, rfl⟩ := hγ
    refine ⟨?_, ?_, ?_⟩ <;> rw [map_apply] <;> simp [ModularGroup.coe_T_zpow]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨ModularGroup.T ^ ((g 0 1).val : ℤ), ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff]
      exact ⟨_, rfl⟩
    · ext i j
      rw [map_apply]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h00, h10, h11, ZMod.natCast_zmod_val]

section Unipotent

variable {R : Type*} [CommRing R]

theorem mul_apply_10_of_left (a M : SL(2, R)) (ha : a 1 0 = 0) (ha1 : a 1 1 = 1) : (a * M) 1 0 = M 1 0 := by
  show ((a : Matrix (Fin 2) (Fin 2) R) * M) 1 0 = M 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ha1]

theorem mul_apply_11_of_left (a M : SL(2, R)) (ha : a 1 0 = 0) (ha1 : a 1 1 = 1) : (a * M) 1 1 = M 1 1 := by
  show ((a : Matrix (Fin 2) (Fin 2) R) * M) 1 1 = M 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ha1]

theorem mul_apply_00_of_left (a M : SL(2, R)) (ha0 : a 0 0 = 1) : (a * M) 0 0 = M 0 0 + a 0 1 * M 1 0 := by
  show ((a : Matrix (Fin 2) (Fin 2) R) * M) 0 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha0]

theorem mul_apply_01_of_left (a M : SL(2, R)) (ha0 : a 0 0 = 1) : (a * M) 0 1 = M 0 1 + a 0 1 * M 1 1 := by
  show ((a : Matrix (Fin 2) (Fin 2) R) * M) 0 1 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha0]

theorem mul_apply_10_of_right (M b : SL(2, R)) (hb0 : b 0 0 = 1) (hb : b 1 0 = 0) : (M * b) 1 0 = M 1 0 := by
  show ((M : Matrix (Fin 2) (Fin 2) R) * b) 1 0 = M 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb0, hb]

theorem mul_apply_00_of_right (M b : SL(2, R)) (hb0 : b 0 0 = 1) (hb : b 1 0 = 0) : (M * b) 0 0 = M 0 0 := by
  show ((M : Matrix (Fin 2) (Fin 2) R) * b) 0 0 = M 0 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb0, hb]

theorem mul_apply_11_of_right (M b : SL(2, R)) (hb1 : b 1 1 = 1) : (M * b) 1 1 = M 1 0 * b 0 1 + M 1 1 := by
  show ((M : Matrix (Fin 2) (Fin 2) R) * b) 1 1 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb1]

theorem mul_apply_01_of_right (M b : SL(2, R)) (hb1 : b 1 1 = 1) : (M * b) 0 1 = M 0 0 * b 0 1 + M 0 1 := by
  show ((M : Matrix (Fin 2) (Fin 2) R) * b) 0 1 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb1]

theorem det_eq (M : SL(2, R)) : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
  have := M.prop
  rw [Matrix.det_fin_two] at this
  exact this

def uni (s : R) : SL(2, R) := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[scoped simp] theorem uni_00 (s : R) : (uni s) 0 0 = 1 := rfl
@[scoped simp] theorem uni_01 (s : R) : (uni s) 0 1 = s := rfl
@[scoped simp] theorem uni_10 (s : R) : (uni s) 1 0 = 0 := rfl
@[scoped simp] theorem uni_11 (s : R) : (uni s) 1 1 = 1 := rfl

end Unipotent

end CuspKit
p2m_reactivate "P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_mul_of_coprime.CuspKit"

namespace CuspC4

theorem natCard_quotient_prod {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (H₁ K₁ : Subgroup G₁) (H₂ K₂ : Subgroup G₂) :
    Nat.card (DoubleCoset.Quotient ((H₁.prod H₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂))) =
      Nat.card (DoubleCoset.Quotient (H₁ : Set G₁) (K₁ : Set G₁)) *
        Nat.card (DoubleCoset.Quotient (H₂ : Set G₂) (K₂ : Set G₂)) := by
  rw [← Nat.card_prod]
  let φ : DoubleCoset.Quotient ((H₁.prod H₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) →
      DoubleCoset.Quotient (H₁ : Set G₁) (K₁ : Set G₁) × DoubleCoset.Quotient (H₂ : Set G₂) (K₂ : Set G₂) :=
    Quotient.lift (fun g => (DoubleCoset.mk H₁ K₁ g.1, DoubleCoset.mk H₂ K₂ g.2)) (fun x y hxy => by
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp hxy
      exact Prod.ext ((DoubleCoset.eq _ _ _ _).mpr ⟨a.1, ha.1, b.1, hb.1, rfl⟩)
        ((DoubleCoset.eq _ _ _ _).mpr ⟨a.2, ha.2, b.2, hb.2, rfl⟩))
  have hφ : ∀ g : G₁ × G₂, φ (DoubleCoset.mk (H₁.prod H₂) (K₁.prod K₂) g) = (DoubleCoset.mk H₁ K₁ g.1, DoubleCoset.mk H₂ K₂ g.2) :=
    fun _ => rfl
  refine Nat.card_congr (Equiv.ofBijective φ ⟨?_, ?_⟩)
  · intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn' with | h x => ?_
    induction q₂ using Quotient.inductionOn' with | h y => ?_
    change φ (DoubleCoset.mk _ _ x) = φ (DoubleCoset.mk _ _ y) at h
    rw [hφ, hφ, Prod.mk.injEq, DoubleCoset.eq, DoubleCoset.eq] at h
    obtain ⟨⟨a₁, ha₁, b₁, hb₁, h₁⟩, ⟨a₂, ha₂, b₂, hb₂, h₂⟩⟩ := h
    change DoubleCoset.mk _ _ x = DoubleCoset.mk _ _ y
    rw [DoubleCoset.eq]
    exact ⟨(a₁, a₂), ⟨ha₁, ha₂⟩, (b₁, b₂), ⟨hb₁, hb₂⟩, Prod.ext h₁ h₂⟩
  · rintro ⟨q₁, q₂⟩
    induction q₁ using Quotient.inductionOn' with | h x => ?_
    induction q₂ using Quotient.inductionOn' with | h y => ?_
    exact ⟨DoubleCoset.mk _ _ (x, y), hφ (x, y)⟩

theorem natCard_quotient_eq_of_mulEquiv {G Q : Type*} [Group G] [Group Q] (e : G ≃* Q) (H K : Subgroup G) :
    Nat.card (DoubleCoset.Quotient (H : Set G) (K : Set G)) =
      Nat.card (DoubleCoset.Quotient (H.map e.toMonoidHom : Set Q) (K.map e.toMonoidHom : Set Q)) := by
  let φ : DoubleCoset.Quotient (H : Set G) (K : Set G) → DoubleCoset.Quotient (H.map e.toMonoidHom : Set Q) (K.map e.toMonoidHom : Set Q) :=
    Quotient.map' e (fun x y hxy => by
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp hxy
      exact DoubleCoset.rel_iff.mpr ⟨e a, Subgroup.mem_map_of_mem _ ha, e b, Subgroup.mem_map_of_mem _ hb,
        by rw [map_mul, map_mul]⟩)
  have hφ : ∀ x : G, φ (DoubleCoset.mk H K x) = DoubleCoset.mk (H.map e.toMonoidHom) (K.map e.toMonoidHom) (e x) := fun _ => rfl
  refine Nat.card_congr (Equiv.ofBijective φ ⟨?_, ?_⟩)
  · intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn' with | h x => ?_
    induction q₂ using Quotient.inductionOn' with | h y => ?_
    change φ (DoubleCoset.mk H K x) = φ (DoubleCoset.mk H K y) at h
    rw [hφ, hφ, DoubleCoset.eq] at h
    obtain ⟨a', ha', b', hb', hy⟩ := h
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
    change DoubleCoset.mk H K x = DoubleCoset.mk H K y
    rw [DoubleCoset.eq]
    refine ⟨a, ha, b, hb, e.injective ?_⟩
    simpa [map_mul] using hy
  · intro q
    induction q using Quotient.inductionOn' with | h z => ?_
    obtain ⟨x, rfl⟩ := e.surjective z
    exact ⟨DoubleCoset.mk H K x, hφ x⟩

theorem sl_map_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : SL(2, R)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.map f g) i j = f (g i j) := by
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

section CRT

variable (M n : ℕ) (hMn : M.Coprime n)

noncomputable def crtHom : SL(2, ZMod (M * n)) →* SL(2, ZMod M) × SL(2, ZMod n) :=
  (Matrix.SpecialLinearGroup.map ((RingHom.fst (ZMod M) (ZMod n)).comp (ZMod.chineseRemainder hMn).toRingHom)).prod
    (Matrix.SpecialLinearGroup.map ((RingHom.snd (ZMod M) (ZMod n)).comp (ZMod.chineseRemainder hMn).toRingHom))

theorem crtHom_fst_apply (g : SL(2, ZMod (M * n))) (i j : Fin 2) :
    (crtHom M n hMn g).1 i j = (ZMod.chineseRemainder hMn (g i j)).1 := by
  simp [crtHom, sl_map_apply]

theorem crtHom_snd_apply (g : SL(2, ZMod (M * n))) (i j : Fin 2) :
    (crtHom M n hMn g).2 i j = (ZMod.chineseRemainder hMn (g i j)).2 := by
  simp [crtHom, sl_map_apply]

theorem crtHom_injective : Function.Injective (crtHom M n hMn) := by
  intro g g' h
  ext i j
  apply (ZMod.chineseRemainder hMn).injective
  exact Prod.ext (by rw [← crtHom_fst_apply, ← crtHom_fst_apply, h]) (by rw [← crtHom_snd_apply, ← crtHom_snd_apply, h])

theorem crtHom_surjective : Function.Surjective (crtHom M n hMn) := by
  rintro ⟨g₁, g₂⟩
  let P : Matrix (Fin 2) (Fin 2) (ZMod M × ZMod n) := fun i j => ((g₁ i j, g₂ i j) : ZMod M × ZMod n)
  let A : Matrix (Fin 2) (Fin 2) (ZMod (M * n)) := P.map (ZMod.chineseRemainder hMn).symm
  have hAP : A.map (ZMod.chineseRemainder hMn).toRingHom = P := by
    ext i j <;> simp [A, P]
  have hP1 : P.map (RingHom.fst (ZMod M) (ZMod n)) = (g₁ : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    ext i j; simp [P]
  have hP2 : P.map (RingHom.snd (ZMod M) (ZMod n)) = (g₂ : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
    ext i j; simp [P]
  have hPdet : P.det = 1 := by
    refine Prod.ext ?_ ?_
    · have h1 := RingHom.map_det (RingHom.fst (ZMod M) (ZMod n)) P
      rw [RingHom.mapMatrix_apply, hP1, Matrix.SpecialLinearGroup.det_coe] at h1
      simpa using h1
    · have h1 := RingHom.map_det (RingHom.snd (ZMod M) (ZMod n)) P
      rw [RingHom.mapMatrix_apply, hP2, Matrix.SpecialLinearGroup.det_coe] at h1
      simpa using h1
  have hdet : A.det = 1 := by
    apply (ZMod.chineseRemainder hMn).injective
    have h2 := RingHom.map_det (ZMod.chineseRemainder hMn).toRingHom A
    rw [RingHom.mapMatrix_apply, hAP, hPdet] at h2
    simpa using h2
  refine ⟨⟨A, hdet⟩, Prod.ext ?_ ?_⟩
  · ext i j
    rw [crtHom_fst_apply]
    simp [A, P]
  · ext i j
    rw [crtHom_snd_apply]
    simp [A, P]

noncomputable def crtEquiv : SL(2, ZMod (M * n)) ≃* SL(2, ZMod M) × SL(2, ZMod n) :=
  MulEquiv.ofBijective (crtHom M n hMn) ⟨crtHom_injective M n hMn, crtHom_surjective M n hMn⟩

theorem apply_eq_iff (g : SL(2, ZMod (M * n))) (i j : Fin 2) (c : ZMod (M * n)) :
    g i j = c ↔ (crtHom M n hMn g).1 i j = (ZMod.chineseRemainder hMn c).1 ∧
      (crtHom M n hMn g).2 i j = (ZMod.chineseRemainder hMn c).2 := by
  rw [crtHom_fst_apply, crtHom_snd_apply, ← (ZMod.chineseRemainder hMn).injective.eq_iff, Prod.ext_iff]

end CRT
p2m_reactivate "P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_mul_of_coprime.CuspKit"

theorem map_crtEquiv_eq_prod (M n : ℕ) [NeZero M] [NeZero n] (hMn : M.Coprime n)
    (S : Subgroup SL(2, ZMod (M * n))) (S₁ : Subgroup SL(2, ZMod M)) (S₂ : Subgroup SL(2, ZMod n))
    (hS : ∀ g, g ∈ S ↔ g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1)
    (hS₁ : ∀ g, g ∈ S₁ ↔ g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1)
    (hS₂ : ∀ g, g ∈ S₂ ↔ g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1) :
    S.map (crtEquiv M n hMn).toMonoidHom = S₁.prod S₂ := by
  ext ⟨g₁, g₂⟩
  rw [Subgroup.mem_map_equiv, Subgroup.mem_prod, hS, hS₁, hS₂]
  have hg : crtHom M n hMn ((crtEquiv M n hMn).symm (g₁, g₂)) = (g₁, g₂) :=
    (crtEquiv M n hMn).apply_symm_apply (g₁, g₂)
  simp only [apply_eq_iff M n hMn, hg, map_one, map_zero, Prod.fst_one, Prod.snd_one, Prod.fst_zero, Prod.snd_zero]
  tauto

end CuspC4
p2m_reactivate "P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_mul_of_coprime.CuspKit"

theorem solution
    (M n : ℕ) [NeZero M] [NeZero n] (hMn : M.Coprime n) :
    Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 (M * n)).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (M * n))))) : Set SL(2, ZMod (M * n))) (((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (M * n))))) : Set SL(2, ZMod (M * n)))) =
      Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 M).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M)))) : Set SL(2, ZMod M)) (((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M)))) : Set SL(2, ZMod M))) * Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 n).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod n)))) : Set SL(2, ZMod n)) (((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod n)))) : Set SL(2, ZMod n))) := by
  rw [CuspC4.natCard_quotient_eq_of_mulEquiv (CuspC4.crtEquiv M n hMn),
    CuspC4.map_crtEquiv_eq_prod M n hMn _
      ((CongruenceSubgroup.Gamma1 M).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M))))
      ((CongruenceSubgroup.Gamma1 n).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod n))))
      (CuspKit.mem_map_gamma1_iff (M * n)) (CuspKit.mem_map_gamma1_iff M) (CuspKit.mem_map_gamma1_iff n),
    CuspC4.map_crtEquiv_eq_prod M n hMn _
      ((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M))))
      ((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod n))))
      (CuspKit.mem_map_zpowers_T_iff (M * n)) (CuspKit.mem_map_zpowers_T_iff M) (CuspKit.mem_map_zpowers_T_iff n),
    CuspC4.natCard_quotient_prod]

#print axioms solution

end S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_mul_of_coprime
end P2MW
export P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_mul_of_coprime (solution)
