-- Prove2me | solution 1 for GOSNIZK.DLINCommit.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T14:53:00.998775+00:00
-- url     : https://prove2.me/submissions/992ddaa2-735e-48a2-b7f7-d006cd8a19cf

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Properties

set_option autoImplicit false

namespace DLINAux

open GOSNIZK.DLINCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

theorem orderOf_g (S : DLINSetup G GT) : orderOf S.g = S.p := by
  rw [orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, S.card_G]

theorem orderOf_E (S : DLINSetup G GT) : orderOf (S.e S.g S.g) = S.p := by
  rw [orderOf_eq_card_of_forall_mem_zpowers S.he, Nat.card_eq_fintype_card, S.card_GT]

theorem powG_mod (S : DLINSetup G GT) (y : G) (k : ℕ) : y ^ (k % S.p) = y ^ k := by
  have := pow_mod_card y k
  rwa [S.card_G] at this

theorem powT_mod (S : DLINSetup G GT) (y : GT) (k : ℕ) : y ^ (k % S.p) = y ^ k := by
  have := pow_mod_card y k
  rwa [S.card_GT] at this

theorem g_mul (S : DLINSetup G GT) (a b : ZMod S.p) :
    S.g ^ a.val * S.g ^ b.val = S.g ^ (a + b).val := by
  rw [ZMod.val_add, powG_mod, pow_add]

theorem g_pow (S : DLINSetup G GT) (a b : ZMod S.p) :
    (S.g ^ a.val) ^ b.val = S.g ^ (a * b).val := by
  rw [ZMod.val_mul, powG_mod, pow_mul]

theorem E_mul (S : DLINSetup G GT) (a b : ZMod S.p) :
    S.e S.g S.g ^ a.val * S.e S.g S.g ^ b.val = S.e S.g S.g ^ (a + b).val := by
  rw [ZMod.val_add, powT_mod, pow_add]

theorem E_pow (S : DLINSetup G GT) (a b : ZMod S.p) :
    (S.e S.g S.g ^ a.val) ^ b.val = S.e S.g S.g ^ (a * b).val := by
  rw [ZMod.val_mul, powT_mod, pow_mul]

theorem powG_nat (S : DLINSetup G GT) (y : G) (k : ℕ) :
    y ^ ((k : ZMod S.p)).val = y ^ k := by
  rw [ZMod.val_natCast, powG_mod]

theorem g_inj (S : DLINSetup G GT) {a b : ZMod S.p} (h : S.g ^ a.val = S.g ^ b.val) : a = b := by
  rw [pow_eq_pow_iff_modEq, orderOf_g] at h
  apply ZMod.val_injective
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h

theorem E_inj (S : DLINSetup G GT) {a b : ZMod S.p}
    (h : S.e S.g S.g ^ a.val = S.e S.g S.g ^ b.val) : a = b := by
  rw [pow_eq_pow_iff_modEq, orderOf_E] at h
  apply ZMod.val_injective
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h

theorem g_eq (S : DLINSetup G GT) {a b : ZMod S.p} (h : a = b) : S.g ^ a.val = S.g ^ b.val := by
  rw [h]

theorem E_eq (S : DLINSetup G GT) {a b : ZMod S.p} (h : a = b) :
    S.e S.g S.g ^ a.val = S.e S.g S.g ^ b.val := by
  rw [h]

theorem exists_exp (S : DLINSetup G GT) (y : G) : ∃ a : ZMod S.p, y = S.g ^ a.val := by
  have hy := (mem_powers_iff_mem_zpowers (x := S.g) (y := y)).2 (S.hg y)
  obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff y S.g |>.1 hy
  exact ⟨(k : ZMod S.p), by rw [powG_nat, hk]⟩

theorem g_inv (S : DLINSetup G GT) (a : ZMod S.p) : (S.g ^ a.val)⁻¹ = S.g ^ (-a).val := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [g_mul, neg_add_cancel, ZMod.val_zero, pow_zero]

theorem e_pow (S : DLINSetup G GT) (a b : ZMod S.p) :
    S.e (S.g ^ a.val) (S.g ^ b.val) = S.e S.g S.g ^ (a * b).val := by
  rw [map_pow, map_pow S.e, MonoidHom.pow_apply, E_pow, mul_comm]

theorem e_gl (S : DLINSetup G GT) (b : ZMod S.p) :
    S.e S.g (S.g ^ b.val) = S.e S.g S.g ^ b.val := by
  rw [map_pow]

/-- the common shape of binding and hiding keys -/
def K (S : DLINSetup G GT) (x y ru sv W : ZMod S.p) : CommitKey G :=
  { f := S.g ^ x.val, h := S.g ^ y.val, u := (S.g ^ x.val) ^ ru.val, v := (S.g ^ y.val) ^ sv.val,
    w := S.g ^ W.val }

theorem key_form (S : DLINSetup G GT) (ck : CommitKey G)
    (hk : (∃ xk, S.IsBindingKey ck xk) ∨ (∃ tk, S.IsHidingKey ck tk)) :
    ∃ x y ru sv W : ZMod S.p, ck = K S x y ru sv W := by
  rcases hk with ⟨⟨x, y, z⟩, _, _, _, ru, sv, rfl⟩ | ⟨⟨ru, sv⟩, x, y, _, _, rfl⟩
  · exact ⟨x, y, ru, sv, ru + sv + z, rfl⟩
  · exact ⟨x, y, ru, sv, ru + sv, rfl⟩

theorem map_equiv_unif {α : Type*} [Fintype α] [Nonempty α] (σ : α ≃ α) :
    (PMF.uniformOfFintype α).map σ = PMF.uniformOfFintype α := by
  ext x
  rw [PMF.map_apply, tsum_eq_single (σ.symm x)]
  · simp
  · intro b hb
    have : x ≠ σ b := by
      intro h
      apply hb
      rw [h, Equiv.symm_apply_apply]
    simp [this]

theorem map_shift (S : DLINSetup G GT) {β : Type*} (F : ZMod S.p → β) (c : ZMod S.p) :
    (PMF.uniformOfFintype (ZMod S.p)).map (fun t => F (t + c)) =
      (PMF.uniformOfFintype (ZMod S.p)).map F := by
  have : (fun t => F (t + c)) = F ∘ (Equiv.addRight c) := rfl
  rw [this, ← PMF.map_comp, map_equiv_unif]

theorem homomorphic (S : DLINSetup G GT) : S.Homomorphic := by
  intro ck hk m₁ r₁ s₁ m₂ r₂ s₂
  obtain ⟨x, y, ru, sv, W, rfl⟩ := key_form S ck hk
  simp only [DLINSetup.com, K, g_pow, g_mul, Prod.mk_mul_mk, Prod.mk.injEq]
  refine ⟨g_eq S ?_, g_eq S ?_, g_eq S ?_⟩ <;> ring

theorem binding (S : DLINSetup G GT) : S.PerfectBinding := by
  intro ck xk hb m₁ r₁ s₁ m₂ r₂ s₂ hc
  obtain ⟨x, y, z⟩ := xk
  obtain ⟨hx, hy, hz, ru, sv, rfl⟩ := hb
  simp only [DLINSetup.com, DLINSetup.bindingKey, g_pow, g_mul, Prod.mk.injEq] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  have e1 := g_inj S h1
  have e2 := g_inj S h2
  have e3 := g_inj S h3
  have hx' : (x : ZMod S.p) ≠ 0 := hx
  have hy' : (y : ZMod S.p) ≠ 0 := hy
  have hz' : (z : ZMod S.p) ≠ 0 := hz
  have a1 : ru * m₁ + r₁ = ru * m₂ + r₂ := by
    apply mul_left_cancel₀ hx'
    linear_combination e1
  have a2 : sv * m₁ + s₁ = sv * m₂ + s₂ := by
    apply mul_left_cancel₀ hy'
    linear_combination e2
  apply mul_left_cancel₀ hz'
  linear_combination e3 - a1 - a2

theorem trapdoor (S : DLINSetup G GT) : S.PerfectTrapdoorOpening := by
  intro ck tk hh m₁ m₂ ρ₁
  obtain ⟨ru, sv⟩ := tk
  obtain ⟨x, y, _, _, rfl⟩ := hh
  simp only [DLINSetup.com, DLINSetup.Topen, DLINSetup.hidingKey, g_pow, g_mul, Prod.mk.injEq]
  refine ⟨g_eq S ?_, g_eq S ?_, g_eq S ?_⟩ <;> ring

theorem trapdoor_indist (S : DLINSetup G GT) : S.PerfectTrapdoorOpeningIndist := by
  intro ck tk _ m₁ m₂
  have : (fun ρ₁ : ZMod S.p × ZMod S.p => S.Topen tk m₁ ρ₁ m₂) =
      ⇑(Equiv.prodCongr (Equiv.subRight ((m₂ - m₁) * tk.1)) (Equiv.subRight ((m₂ - m₁) * tk.2))) := by
    funext ρ
    rfl
  rw [this, map_equiv_unif]

theorem completeness (S : DLINSetup G GT) : S.PerfectCompleteness := by
  intro ck hk m hm r s t
  obtain ⟨x, y, ru, sv, W, rfl⟩ := key_form S ck hk
  simp only [DLINSetup.V01, DLINSetup.com, DLINSetup.P01, K, g_pow, g_mul, g_inv, e_pow, e_gl, E_mul]
  rcases hm with rfl | rfl <;>
  · refine ⟨E_eq S ?_, E_eq S ?_, E_eq S ?_, E_eq S ?_, E_eq S ?_, E_eq S ?_⟩ <;> ring

theorem extract (S : DLINSetup G GT) : S.PerfectExtractability := by
  classical
  intro ck xk hb m _ r s
  obtain ⟨x, y, z⟩ := xk
  obtain ⟨hx, hy, hz, ru, sv, rfl⟩ := hb
  have hx' : (x : ZMod S.p) ≠ 0 := hx
  have hy' : (y : ZMod S.p) ≠ 0 := hy
  have hz' : (z : ZMod S.p) ≠ 0 := hz
  have hd : (S.com (S.bindingKey x y ru sv z) m r s).2.2 *
      (S.com (S.bindingKey x y ru sv z) m r s).1 ^ (-1 / x).val *
      (S.com (S.bindingKey x y ru sv z) m r s).2.1 ^ (-1 / y).val = S.g ^ (z * m).val := by
    simp only [DLINSetup.com, DLINSetup.bindingKey, g_pow, g_mul]
    apply g_eq S
    field_simp
    ring
  have key : ∀ k : ℕ, (S.g ^ z.val) ^ k = S.g ^ (z * m).val ↔ (k : ZMod S.p) = m := by
    intro k
    rw [← powG_nat S (S.g ^ z.val) k, g_pow]
    constructor
    · intro h
      exact mul_left_cancel₀ hz' (g_inj S h)
    · intro h
      rw [h]
  unfold DLINSetup.Ext
  split_ifs with hc
  · have hs := (Nat.find_spec hc).2
    simp only at hs
    exact (key _).1 (hs.trans hd)
  · exfalso
    apply hc
    refine ⟨m.val, ZMod.val_lt m, ?_⟩
    exact ((key _).2 (ZMod.natCast_zmod_val m)).trans hd.symm

theorem soundness (S : DLINSetup G GT) : S.PerfectSoundness := by
  intro ck xk hb c π hV
  obtain ⟨x, y, z⟩ := xk
  obtain ⟨hx, hy, hz, ru, sv, rfl⟩ := hb
  have hx' : (x : ZMod S.p) ≠ 0 := hx
  have hy' : (y : ZMod S.p) ≠ 0 := hy
  have hz' : (z : ZMod S.p) ≠ 0 := hz
  obtain ⟨c1, c2, c3⟩ := c
  obtain ⟨p11, p12, p13, p21, p22, p23⟩ := π
  obtain ⟨A, rfl⟩ := exists_exp S c1
  obtain ⟨B, rfl⟩ := exists_exp S c2
  obtain ⟨C, rfl⟩ := exists_exp S c3
  obtain ⟨P11, rfl⟩ := exists_exp S p11
  obtain ⟨P12, rfl⟩ := exists_exp S p12
  obtain ⟨P13, rfl⟩ := exists_exp S p13
  obtain ⟨P21, rfl⟩ := exists_exp S p21
  obtain ⟨P22, rfl⟩ := exists_exp S p22
  obtain ⟨P23, rfl⟩ := exists_exp S p23
  have hex : ∃ m r s : ZMod S.p, A = x * (ru * m + r) ∧ B = y * (sv * m + s) ∧
      C = (ru + sv + z) * m + (r + s) := by
    refine ⟨(C - A / x - B / y) / z, A / x - ru * ((C - A / x - B / y) / z),
      B / y - sv * ((C - A / x - B / y) / z), ?_, ?_, ?_⟩
    · field_simp
      ring
    · field_simp
      ring
    · field_simp
      ring
  obtain ⟨m, r, s, rfl, rfl, rfl⟩ := hex
  simp only [DLINSetup.V01, DLINSetup.bindingKey, g_pow, g_mul, g_inv, e_pow, e_gl, E_mul] at hV
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hV
  have e1 := E_inj S h1
  have e2 := E_inj S h2
  have e3 := E_inj S h3
  have e4 := E_inj S h4
  have e5 := E_inj S h5
  have e6 := E_inj S h6
  have hq : x ^ 2 * y ^ 2 * z ^ 2 * (m * (m - 1)) = 0 := by
    linear_combination (x * y ^ 2) * e4 + (x ^ 2 * y) * e6 - (x ^ 2 * y ^ 2) * e5 - y ^ 2 * e1 -
      x ^ 2 * e3 - (x * y) * e2
  have hm : m * (m - 1) = 0 := by
    rcases mul_eq_zero.1 hq with h | h
    · exfalso
      simp_all
    · exact h
  refine ⟨m, r, s, ?_, ?_⟩
  · rcases mul_eq_zero.1 hm with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  · simp only [DLINSetup.com, DLINSetup.bindingKey, g_pow, g_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | (apply g_eq S; ring)

/-- the WI identity: on a hiding key, the proof made with the 0-opening equals the proof made with the
1-opening and shifted randomness -/
theorem wi_key (S : DLINSetup G GT) (x y ru sv r₀ s₀ r₁ s₁ : ZMod S.p) (hx : x ≠ 0) (hy : y ≠ 0)
    (hc : S.com (S.hidingKey x y ru sv) 0 r₀ s₀ = S.com (S.hidingKey x y ru sv) 1 r₁ s₁) (t : ZMod S.p) :
    S.P01 (S.hidingKey x y ru sv) 0 (r₀, s₀) t =
      S.P01 (S.hidingKey x y ru sv) 1 (r₁, s₁) (t + (r₀ * s₁ - s₀ * r₁)) := by
  simp only [DLINSetup.com, DLINSetup.hidingKey, g_pow, g_mul, Prod.mk.injEq] at hc
  obtain ⟨h1, h2, _⟩ := hc
  have e1 := g_inj S h1
  have e2 := g_inj S h2
  have a1 : ru = r₀ - r₁ := by
    apply mul_left_cancel₀ hx
    linear_combination -e1
  have a2 : sv = s₀ - s₁ := by
    apply mul_left_cancel₀ hy
    linear_combination -e2
  subst a1 a2
  simp only [DLINSetup.P01, DLINSetup.hidingKey, g_pow, g_mul, Proof01.mk.injEq]
  refine ⟨g_eq S ?_, g_eq S ?_, g_eq S ?_, g_eq S ?_, g_eq S ?_, g_eq S ?_⟩ <;> ring

theorem wi (S : DLINSetup G GT) : S.PerfectWI := by
  intro ck tk hh ρ₀ ρ₁ hc
  obtain ⟨ru, sv⟩ := tk
  obtain ⟨x, y, hx, hy, rfl⟩ := hh
  obtain ⟨r₀, s₀⟩ := ρ₀
  obtain ⟨r₁, s₁⟩ := ρ₁
  have hk := wi_key S x y ru sv r₀ s₀ r₁ s₁ hx hy hc
  have : S.P01 (S.hidingKey x y ru sv) 0 (r₀, s₀) =
      fun t => S.P01 (S.hidingKey x y ru sv) 1 (r₁, s₁) (t + (r₀ * s₁ - s₀ * r₁)) := funext hk
  rw [this, map_shift S]

theorem newi (S : DLINSetup G GT) : S.PerfectNonErasureWI S.S01 := by
  intro ck tk hh m hm ρ₀ ρ₁ hc
  obtain ⟨ru, sv⟩ := tk
  obtain ⟨x, y, hx, hy, rfl⟩ := hh
  obtain ⟨r₀, s₀⟩ := ρ₀
  obtain ⟨r₁, s₁⟩ := ρ₁
  rcases hm with rfl | rfl
  · rw [sub_zero] at hc
    have hk := wi_key S x y ru sv r₀ s₀ r₁ s₁ hx hy hc
    have : (fun t₀ => (S.P01 (S.hidingKey x y ru sv) 0 (r₀, s₀) t₀, S.S01 0 (r₀, s₀) (r₁, s₁) t₀)) =
        fun t => (fun t₁ => (S.P01 (S.hidingKey x y ru sv) (1 - 0) (r₁, s₁) t₁, t₁))
          (t + (r₀ * s₁ - s₀ * r₁)) := by
      funext t
      rw [DLINSetup.S01, if_pos rfl, sub_zero, hk]
      congr 1
      ring
    rw [this]
    exact map_shift S (fun t₁ => (S.P01 (S.hidingKey x y ru sv) (1 - 0) (r₁, s₁) t₁, t₁))
      (r₀ * s₁ - s₀ * r₁)
  · rw [sub_self] at hc ⊢
    have hk := wi_key S x y ru sv r₁ s₁ r₀ s₀ hx hy hc.symm
    have h10 : (1 : ZMod S.p) ≠ 0 := one_ne_zero
    rw [← map_shift S (fun t₁ => (S.P01 (S.hidingKey x y ru sv) 0 (r₁, s₁) t₁, t₁))
      (-(r₁ * s₀ - s₁ * r₀))]
    congr 1
    funext t
    simp only [DLINSetup.S01, if_neg h10]
    rw [hk]
    congr 1
    · congr 1
      ring
    · ring

end DLINAux

open GOSNIZK.DLINCommit in
theorem solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : DLINSetup G GT) :
    S.Homomorphic ∧ S.PerfectBinding ∧ S.PerfectExtractability ∧ S.PerfectTrapdoorOpening ∧
      S.PerfectTrapdoorOpeningIndist ∧ S.PerfectCompleteness ∧ S.PerfectSoundness ∧ S.PerfectWI ∧
      S.PerfectNonErasureWI S.S01 := by
  exact ⟨DLINAux.homomorphic S, DLINAux.binding S, DLINAux.extract S, DLINAux.trapdoor S,
      DLINAux.trapdoor_indist S, DLINAux.completeness S, DLINAux.soundness S, DLINAux.wi S,
      DLINAux.newi S⟩
