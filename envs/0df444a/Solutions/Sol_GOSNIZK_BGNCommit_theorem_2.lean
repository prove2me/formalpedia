-- Prove2me | solution 1 for GOSNIZK.BGNCommit.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T11:33:55.82199+00:00
-- url     : https://prove2.me/submissions/218bfc7c-950a-445c-828c-88637c71a115

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

set_option autoImplicit false

namespace BGNAux

open GOSNIZK.BGNCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

theorem orderOf_g (S : BGNSetup G GT) : orderOf S.g = S.n := by
  rw [orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, S.card_G]

theorem orderOf_E (S : BGNSetup G GT) : orderOf (S.e S.g S.g) = S.n := by
  rw [orderOf_eq_card_of_forall_mem_zpowers S.he, Nat.card_eq_fintype_card, S.card_GT]

theorem powG_mod (S : BGNSetup G GT) (y : G) (k : ℕ) : y ^ (k % S.n) = y ^ k := by
  have := pow_mod_card y k
  rwa [S.card_G] at this

theorem powT_mod (S : BGNSetup G GT) (y : GT) (k : ℕ) : y ^ (k % S.n) = y ^ k := by
  have := pow_mod_card y k
  rwa [S.card_GT] at this

theorem powG_add (S : BGNSetup G GT) (y : G) (a b : ZMod S.n) :
    y ^ (a + b).val = y ^ a.val * y ^ b.val := by
  rw [ZMod.val_add, powG_mod, pow_add]

theorem powG_mul (S : BGNSetup G GT) (y : G) (a b : ZMod S.n) :
    y ^ (a * b).val = (y ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, powG_mod, pow_mul]

theorem powT_mul (S : BGNSetup G GT) (y : GT) (a b : ZMod S.n) :
    y ^ (a * b).val = (y ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, powT_mod, pow_mul]

theorem powG_nat (S : BGNSetup G GT) (y : G) (k : ℕ) :
    y ^ ((k : ZMod S.n)).val = y ^ k := by
  rw [ZMod.val_natCast, powG_mod]

theorem g_inj (S : BGNSetup G GT) {a b : ZMod S.n} (h : S.g ^ a.val = S.g ^ b.val) : a = b := by
  rw [pow_eq_pow_iff_modEq, orderOf_g] at h
  apply ZMod.val_injective
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h

theorem E_inj (S : BGNSetup G GT) {a b : ZMod S.n}
    (h : S.e S.g S.g ^ a.val = S.e S.g S.g ^ b.val) : a = b := by
  rw [pow_eq_pow_iff_modEq, orderOf_E] at h
  apply ZMod.val_injective
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h

theorem exists_exp (S : BGNSetup G GT) (y : G) : ∃ a : ZMod S.n, y = S.g ^ a.val := by
  have hy := (mem_powers_iff_mem_zpowers (x := S.g) (y := y)).2 (S.hg y)
  obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff y S.g |>.1 hy
  exact ⟨(k : ZMod S.n), by rw [powG_nat, hk]⟩

theorem g_mul (S : BGNSetup G GT) (a b : ZMod S.n) :
    S.g ^ a.val * S.g ^ b.val = S.g ^ (a + b).val := (powG_add S _ a b).symm

theorem g_pow (S : BGNSetup G GT) (a b : ZMod S.n) :
    (S.g ^ a.val) ^ b.val = S.g ^ (a * b).val := (powG_mul S _ a b).symm

theorem g_inv (S : BGNSetup G GT) : S.g⁻¹ = S.g ^ ((-1 : ZMod S.n)).val := by
  symm
  apply eq_inv_of_mul_eq_one_left
  have h2 := g_mul S (-1) ((1 : ℕ) : ZMod S.n)
  rw [powG_nat, pow_one] at h2
  rw [h2]
  simp

theorem e_pow (S : BGNSetup G GT) (a b : ZMod S.n) :
    S.e (S.g ^ a.val) (S.g ^ b.val) = S.e S.g S.g ^ (a * b).val := by
  rw [map_pow, map_pow S.e, MonoidHom.pow_apply, powT_mul]

/-- commitment as a single exponent, for `h = g^t` -/
theorem com_eq (S : BGNSetup G GT) (t m r : ZMod S.n) :
    S.com (S.g ^ t.val) m r = S.g ^ (m + t * r).val := by
  unfold BGNSetup.com
  rw [g_pow, g_mul]

theorem P01_eq (S : BGNSetup G GT) (t m r : ZMod S.n) :
    S.P01 (S.g ^ t.val) m r = S.g ^ ((2 * m - 1 + t * r) * r).val := by
  unfold BGNSetup.P01
  rw [g_pow, g_mul, g_pow]

/-- every key considered has the form `g^t` -/
theorem key_exp (S : BGNSetup G GT) (h : G) : ∃ t : ZMod S.n, h = S.g ^ t.val :=
  exists_exp S h

theorem binding_exp (S : BGNSetup G GT) (h : G) (hb : S.IsBindingKey h) :
    ∃ x : ZMod S.q, IsUnit x ∧ h = S.g ^ ((S.p : ZMod S.n) * (x.val : ZMod S.n)).val := by
  obtain ⟨x, hx, rfl⟩ := hb
  refine ⟨x, hx, ?_⟩
  rw [← Nat.cast_mul, powG_nat]

theorem toZp_natCast (S : BGNSetup G GT) (k : ℕ) : S.toZp (k : ZMod S.n) = (k : ZMod S.p) := by
  simp

theorem toZp_p (S : BGNSetup G GT) : S.toZp (S.p : ZMod S.n) = 0 := by
  rw [toZp_natCast, ZMod.natCast_self]

theorem n_zero (S : BGNSetup G GT) : ((S.p : ZMod S.n) * (S.q : ZMod S.n)) = 0 := by
  rw [← Nat.cast_mul]
  exact ZMod.natCast_self _

theorem toZp_val (S : BGNSetup G GT) (z : ZMod S.n) : S.toZp z = (z.val : ZMod S.p) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact toZp_natCast S _

theorem toZp_zero_dvd (S : BGNSetup G GT) (z : ZMod S.n) (hz : S.toZp z = 0) :
    ∃ s : ZMod S.n, z = (S.p : ZMod S.n) * s := by
  rw [toZp_val, ZMod.natCast_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  refine ⟨(k : ZMod S.n), ?_⟩
  rw [← Nat.cast_mul, ← hk, ZMod.natCast_zmod_val]

theorem ext_eq (S : BGNSetup G GT) (z : ZMod S.n) : S.Ext (S.g ^ z.val) = S.toZp z := by
  classical
  have key : ∀ K : ℕ, (S.g ^ z.val) ^ S.q = (S.g ^ S.q) ^ K ↔ z.val ≡ K [MOD S.p] := by
    intro K
    rw [← pow_mul, ← pow_mul, pow_eq_pow_iff_modEq, orderOf_g]
    constructor
    · intro h
      have h' : S.q * z.val ≡ S.q * K [MOD S.q * S.p] := by
        rw [mul_comm S.q z.val, mul_comm S.q S.p]; exact h
      exact Nat.ModEq.mul_left_cancel' S.hq.ne_zero h'
    · intro h
      have h' := Nat.ModEq.mul_left' S.q h
      rw [mul_comm S.q z.val, mul_comm S.q S.p] at h'
      exact h'
  have hex : ∃ k : ℕ, k < S.p ∧ (S.g ^ z.val) ^ S.q = (S.g ^ S.q) ^ k :=
    ⟨z.val % S.p, Nat.mod_lt _ S.hp.pos, (key _).2 (Nat.mod_modEq _ _).symm⟩
  have P' : ∀ k : ℕ, (k < S.p ∧ (S.g ^ z.val) ^ S.q = (S.g ^ S.q) ^ k) →
      ((k : ℕ) : ZMod S.p) = S.toZp z := by
    intro k hk
    rw [toZp_val]
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).2 ((key k).1 hk.2)).symm
  unfold BGNSetup.Ext
  rw [dif_pos hex]
  exact P' _ (Nat.find_spec hex)

end BGNAux

open GOSNIZK.BGNCommit in
theorem solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) :
    -- (1) homomorphic property, on either kind of key
    (∀ h : G, (S.IsBindingKey h ∨ ∃ x, S.IsHidingKey h x) →
      ∀ m₁ r₁ m₂ r₂ : ZMod S.n, S.com h (m₁ + m₂) (r₁ + r₂) = S.com h m₁ r₁ * S.com h m₂ r₂) ∧
    -- (2) perfect binding (messages live in ℤ_p)
    (∀ h : G, S.IsBindingKey h →
      ∀ m₁ r₁ m₂ r₂ : ZMod S.n, S.com h m₁ r₁ = S.com h m₂ r₂ → S.toZp m₁ = S.toZp m₂) ∧
    -- (3) perfect trapdoor opening
    (∀ (h : G) (x : ZMod S.n), S.IsHidingKey h x →
      ∀ m₁ r₁ m₂ : ZMod S.n, S.com h m₂ (S.Topen x m₁ r₁ m₂) = S.com h m₁ r₁) ∧
    -- (4) perfect trapdoor opening indistinguishability: Topen(m₁, r₁, m₂) with r₁ uniform is uniform
    (∀ (h : G) (x : ZMod S.n), S.IsHidingKey h x →
      ∀ m₁ m₂ : ZMod S.n,
        (PMF.uniformOfFintype (ZMod S.n)).map (fun r₁ => S.Topen x m₁ r₁ m₂) =
          PMF.uniformOfFintype (ZMod S.n)) ∧
    -- (5) perfect completeness, on either kind of key
    (∀ h : G, (S.IsBindingKey h ∨ ∃ x, S.IsHidingKey h x) →
      ∀ m r : ZMod S.n, (m = 0 ∨ m = 1) → S.V01 h (S.com h m r) (S.P01 h m r)) ∧
    -- (6) perfect soundness on binding keys
    (∀ h : G, S.IsBindingKey h →
      ∀ c π : G, S.V01 h c π → ∃ m r : ZMod S.n, (m = 0 ∨ m = 1) ∧ c = S.com h m r) ∧
    -- (7) perfect witness indistinguishability on hiding keys
    (∀ (h : G) (x : ZMod S.n), S.IsHidingKey h x →
      ∀ r₀ r₁ : ZMod S.n, S.com h 0 r₀ = S.com h 1 r₁ → S.P01 h 0 r₀ = S.P01 h 1 r₁) ∧
    -- (8) perfect non-erasure witness indistinguishability (empty proof randomness, S01 trivial)
    (∀ (h : G) (x : ZMod S.n), S.IsHidingKey h x →
      ∀ m r₀ r₁ : ZMod S.n, (m = 0 ∨ m = 1) → S.com h m r₀ = S.com h (1 - m) r₁ →
        S.P01 h m r₀ = S.P01 h (1 - m) r₁) ∧
    -- (9) perfect extractability on binding keys
    (∀ h : G, S.IsBindingKey h →
      ∀ m r : ZMod S.n, (m = 0 ∨ m = 1) → S.Ext (S.com h m r) = S.toZp m) := by
  -- (8) for an arbitrary key
  have wi8 : ∀ (h : G) (m r₀ r₁ : ZMod S.n), S.com h m r₀ = S.com h (1 - m) r₁ →
      S.P01 h m r₀ = S.P01 h (1 - m) r₁ := by
    intro h m r₀ r₁ hc
    obtain ⟨t, rfl⟩ := BGNAux.key_exp S h
    rw [BGNAux.com_eq, BGNAux.com_eq] at hc
    have he := BGNAux.g_inj S hc
    rw [BGNAux.P01_eq, BGNAux.P01_eq]
    congr 2
    linear_combination (r₀ + r₁) * he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1)
    intro h _ m₁ r₁ m₂ r₂
    unfold BGNSetup.com
    rw [BGNAux.powG_add, BGNAux.powG_add]
    exact mul_mul_mul_comm _ _ _ _
  · -- (2)
    intro h hb m₁ r₁ m₂ r₂ hc
    obtain ⟨x, _, rfl⟩ := BGNAux.binding_exp S h hb
    rw [BGNAux.com_eq, BGNAux.com_eq] at hc
    have he := congrArg S.toZp (BGNAux.g_inj S hc)
    simp only [map_add, map_mul, BGNAux.toZp_p, zero_mul, add_zero] at he
    exact he
  · -- (3)
    intro h x hx m₁ r₁ m₂
    obtain ⟨hu, rfl⟩ := hx
    rw [BGNAux.com_eq, BGNAux.com_eq]
    congr 2
    unfold BGNSetup.Topen
    have hxx : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x hu
    linear_combination (m₁ - m₂) * hxx
  · -- (4)
    intro h x _ m₁ m₂
    ext y
    rw [PMF.map_apply]
    unfold BGNSetup.Topen
    have hcond : ∀ r : ZMod S.n, (y = r - (m₂ - m₁) * x⁻¹) ↔ (r = y + (m₂ - m₁) * x⁻¹) := by
      intro r
      constructor
      · intro h1; rw [h1]; ring
      · intro h1; rw [h1]; ring
    simp_rw [hcond]
    rw [tsum_ite_eq]
    simp
  · -- (5)
    intro h _ m r hm
    obtain ⟨t, rfl⟩ := BGNAux.key_exp S h
    unfold BGNSetup.V01
    rw [BGNAux.com_eq, BGNAux.P01_eq, BGNAux.g_inv, BGNAux.g_mul, BGNAux.e_pow, BGNAux.e_pow]
    congr 2
    rcases hm with rfl | rfl <;> ring
  · -- (6)
    intro h hb c π hv
    obtain ⟨x, hxu, rfl⟩ := BGNAux.binding_exp S h hb
    obtain ⟨a, rfl⟩ := BGNAux.exists_exp S c
    obtain ⟨b, rfl⟩ := BGNAux.exists_exp S π
    unfold BGNSetup.V01 at hv
    rw [BGNAux.g_inv, BGNAux.g_mul, BGNAux.e_pow, BGNAux.e_pow] at hv
    have he := congrArg S.toZp (BGNAux.E_inj S hv)
    simp only [map_add, map_mul, BGNAux.toZp_p, zero_mul] at he
    have hm01 : S.toZp a = 0 ∨ S.toZp a = 1 := by
      have h0 : S.toZp a * (S.toZp a - 1) = 0 := by
        rw [map_neg, map_one] at he
        linear_combination he
      rcases mul_eq_zero.1 h0 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.1 h0)
    -- choose m
    obtain ⟨m, hm, hma⟩ : ∃ m : ZMod S.n, (m = 0 ∨ m = 1) ∧ S.toZp (a - m) = 0 := by
      rcases hm01 with h0 | h1
      · exact ⟨0, Or.inl rfl, by rw [sub_zero, h0]⟩
      · exact ⟨1, Or.inr rfl, by rw [map_sub, h1, map_one, sub_self]⟩
    obtain ⟨s, hs⟩ := BGNAux.toZp_zero_dvd S _ hma
    -- inverse of x mod q
    obtain ⟨y, hy⟩ : ∃ y : ZMod S.q, x * y = 1 := ⟨x⁻¹, ZMod.mul_inv_of_unit x hxu⟩
    have hxy : ∃ k : ℕ, x.val * y.val = 1 + S.q * k := by
      have hmod : (x.val * y.val) % S.q = 1 := by
        have hF : Fact (1 < S.q) := ⟨S.hq.one_lt⟩
        have h3 := congrArg ZMod.val hy
        rwa [ZMod.val_mul, ZMod.val_one] at h3
      refine ⟨x.val * y.val / S.q, ?_⟩
      have := Nat.mod_add_div (x.val * y.val) S.q
      rw [hmod] at this
      exact this.symm
    obtain ⟨k, hk⟩ := hxy
    refine ⟨m, s * (y.val : ZMod S.n), hm, ?_⟩
    rw [BGNAux.com_eq]
    congr 2
    have hk' : (x.val : ZMod S.n) * (y.val : ZMod S.n) = 1 + (S.q : ZMod S.n) * (k : ZMod S.n) := by
      rw [← Nat.cast_mul, hk]; push_cast; ring
    have hn := BGNAux.n_zero S
    linear_combination hs - (S.p : ZMod S.n) * s * hk' - s * (k : ZMod S.n) * hn
  · -- (7)
    intro h _ _ r₀ r₁ hc
    have := wi8 h 0 r₀ r₁ (by rw [sub_zero]; exact hc)
    rwa [sub_zero] at this
  · -- (8)
    intro h _ _ m r₀ r₁ _ hc
    exact wi8 h m r₀ r₁ hc
  · -- (9)
    intro h hb m r _
    obtain ⟨x, _, rfl⟩ := BGNAux.binding_exp S h hb
    rw [BGNAux.com_eq]
    rw [BGNAux.ext_eq, map_add, map_mul, map_mul, BGNAux.toZp_p, zero_mul, zero_mul, add_zero]
