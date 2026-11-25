-- Prove2me | solution 3 for DetDLP.lemma_3_2_collision_potential
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:36:59.420844+00:00
-- url     : https://prove2.me/submissions/e4090cbe-29db-4be2-aa23-0e31b360d724

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

open DetDLP

/-! ### Part 1: Elementary analytic and parameter bounds -/

private lemma one_add_pow_le_inv_one_sub {x : ℝ} {m : ℕ} (hx : 0 ≤ x)
    (hmx : (m : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ m ≤ 1 / (1 - (m : ℝ) * x) := by
  by_cases hm : m = 0
  · subst hm; simp
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have hx_le : x ≤ 1 / 2 := by nlinarith
    have h1mx_pos : 0 < 1 - (m : ℝ) * x := by linarith
    have hbern : 1 - (m : ℝ) * x ≤ (1 - x) ^ m := by
      have h := one_add_mul_le_pow (a := -x) (by linarith) m
      rw [← sub_eq_add_neg] at h
      linarith
    have hprod_le : (1 + x) ^ m * (1 - x) ^ m ≤ 1 := by
      rw [← mul_pow]
      have hbase_le : (1 + x) * (1 - x) ≤ 1 := by nlinarith
      have hbase_nn : 0 ≤ (1 + x) * (1 - x) := by nlinarith
      calc ((1 + x) * (1 - x)) ^ m ≤ 1 ^ m := pow_le_pow_left₀ hbase_nn hbase_le m
        _ = 1 := one_pow m
    have hmul : (1 + x) ^ m * (1 - (m : ℝ) * x) ≤ 1 := by
      calc (1 + x) ^ m * (1 - (m : ℝ) * x)
          ≤ (1 + x) ^ m * (1 - x) ^ m :=
            mul_le_mul_of_nonneg_left hbern (by positivity)
        _ ≤ 1 := hprod_le
    rw [le_div_iff₀ h1mx_pos]
    exact hmul

private lemma hashThreshold_params {p n m gord : ℕ} (hp : 2 ≤ p) (hm : 2 ≤ m)
    (hn : 4096 * m ≤ n) (hgord : gord ≤ n + 1) :
    let T := hashThreshold p n m gord
    let θ := (T : ℝ) / (p : ℝ)
    let qblk := qBlk p n T
    1 ≤ T ∧ T ≤ p ∧ 0 < θ ∧ θ ≤ 1 ∧ qblk = (n : ℝ) * θ ∧
      (4096 * m : ℝ) ≤ qblk ∧ 16 * (gord : ℝ) ≤ qblk ^ m := by
  dsimp only
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hn_ge : (8192 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 8192 ≤ n)
  have hgord_le : (gord : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hgord
  have h16g_le_nm : 16 * (gord : ℝ) ≤ (n : ℝ) ^ m := by
    have h1 : 16 * (gord : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ m :=
      pow_le_pow_right₀ (by linarith) hm
    exact le_trans h1 h2
  have hceil_le_n : Nat.ceil ((16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ))) ≤ n := by
    rw [Nat.ceil_le]
    have hnn : 0 ≤ 16 * (gord : ℝ) := by positivity
    calc (16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ))
        ≤ ((n : ℝ) ^ m) ^ ((1 : ℝ) / (m : ℝ)) :=
          Real.rpow_le_rpow hnn h16g_le_nm (by positivity)
      _ = ((n : ℝ) ^ (m : ℝ)) ^ ((1 : ℝ) / (m : ℝ)) := by rw [Real.rpow_natCast]
      _ = (n : ℝ) ^ ((m : ℝ) * ((1 : ℝ) / (m : ℝ))) := by
          rw [← Real.rpow_mul (le_of_lt hn_pos)]
      _ = (n : ℝ) := by
          rw [mul_one_div_cancel (ne_of_gt hm_pos), Real.rpow_one]
  have hqstar_le_n : qStar m gord ≤ n := max_le hn hceil_le_n
  have hqstar_ge_4096m : 4096 * m ≤ qStar m gord := le_max_left _ _
  have hT_le_p : hashThreshold p n m gord ≤ p := by
    unfold hashThreshold
    rw [Nat.ceil_le, div_le_iff₀ hn_pos]
    have hq_le : (qStar m gord : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqstar_le_n
    nlinarith
  have hT_pos : 1 ≤ hashThreshold p n m gord := by
    unfold hashThreshold
    have hpos : (0 : ℝ) < (p : ℝ) * (qStar m gord : ℝ) / (n : ℝ) := by
      have hq_pos : (0 : ℝ) < (qStar m gord : ℝ) := by
        exact_mod_cast (by omega : 0 < qStar m gord)
      positivity
    exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr hpos)
  have hθ_pos : 0 < (hashThreshold p n m gord : ℝ) / (p : ℝ) := by
    have hTr : (0 : ℝ) < (hashThreshold p n m gord : ℝ) := by
      exact_mod_cast (by omega : 0 < hashThreshold p n m gord)
    positivity
  have hθ_le : (hashThreshold p n m gord : ℝ) / (p : ℝ) ≤ 1 := by
    rw [div_le_one hp_pos]
    exact_mod_cast hT_le_p
  have hqblk_eq : qBlk p n (hashThreshold p n m gord) =
      (n : ℝ) * ((hashThreshold p n m gord : ℝ) / (p : ℝ)) := by
    unfold qBlk; ring
  have hqstar_le_qblk : (qStar m gord : ℝ) ≤ qBlk p n (hashThreshold p n m gord) := by
    unfold qBlk hashThreshold
    have hle : (p : ℝ) * (qStar m gord : ℝ) / (n : ℝ) ≤
        (Nat.ceil (((p : ℝ) * (qStar m gord : ℝ)) / (n : ℝ)) : ℝ) :=
      Nat.le_ceil _
    rw [div_le_iff₀ hn_pos] at hle
    rw [le_div_iff₀ hp_pos]
    linarith
  have h4096m_le_qblk : (4096 * m : ℝ) ≤ qBlk p n (hashThreshold p n m gord) := by
    have h : (4096 * m : ℝ) ≤ (qStar m gord : ℝ) := by exact_mod_cast hqstar_ge_4096m
    exact le_trans h hqstar_le_qblk
  have h16g_le_mu : 16 * (gord : ℝ) ≤ (qBlk p n (hashThreshold p n m gord)) ^ m := by
    have hceil_le_qstar : Nat.ceil ((16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ))) ≤ qStar m gord :=
      le_max_right (4096 * m) _
    have hbase : (16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ)) ≤ qBlk p n (hashThreshold p n m gord) := by
      calc (16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ))
          ≤ (Nat.ceil ((16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ))) : ℝ) := Nat.le_ceil _
        _ ≤ (qStar m gord : ℝ) := by exact_mod_cast hceil_le_qstar
        _ ≤ qBlk p n (hashThreshold p n m gord) := hqstar_le_qblk
    have h1 : ((16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ))) ^ m ≤
        (qBlk p n (hashThreshold p n m gord)) ^ m :=
      pow_le_pow_left₀ (by positivity) hbase m
    have h2 : ((16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ))) ^ m = 16 * (gord : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hm_pos),
        Real.rpow_one]
    linarith
  exact ⟨hT_pos, hT_le_p, hθ_pos, hθ_le, hqblk_eq, h4096m_le_qblk, h16g_le_mu⟩

/-! ### Part 2: Exact 1-point and 2-point affine-interval hash counts mod `p` -/

private lemma zmod_affine_val_eq {p : ℕ} [Fact p.Prime] (a : Fin (p - 1)) (b : Fin p) (x : ZMod p) :
    (((a.val + 1 : ℕ) : ZMod p) * x + (b.val : ZMod p)).val =
      ((a.val + 1) * x.val + b.val) % p := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [ZMod.val_add, ZMod.val_mul, ZMod.val_natCast, ZMod.val_natCast]
  simp [Nat.add_mod, Nat.mul_mod]

private lemma affine_hash_1pt_card {p : ℕ} [Fact p.Prime] {T : ℕ} (hTp : T ≤ p) (x : ZMod p) :
    (Finset.univ.filter fun ab : Fin (p - 1) × Fin p =>
      ((ab.1.val + 1) * x.val + ab.2.val) % p < T).card = (p - 1) * T := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ a : Fin (p - 1),
      (∑ b : Fin p, if ((a.val + 1) * x.val + b.val) % p < T then 1 else 0) = T := by
    intro a
    let e : Fin p ≃ ZMod p :=
      { toFun := fun b => (b.val : ZMod p)
        invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
        left_inv := fun b => Fin.ext (by dsimp only; rw [ZMod.val_natCast, Nat.mod_eq_of_lt b.isLt])
        right_inv := fun z => ZMod.natCast_zmod_val z }
    let shift : ZMod p ≃ ZMod p := Equiv.addLeft (((a.val + 1 : ℕ) : ZMod p) * x)
    let φ : Fin p ≃ Fin p := (e.trans shift).trans e.symm
    have hval : ∀ b : Fin p, (φ b).val = ((a.val + 1) * x.val + b.val) % p := by
      intro b
      exact zmod_affine_val_eq a b x
    calc ∑ b : Fin p, (if ((a.val + 1) * x.val + b.val) % p < T then 1 else 0)
        = ∑ b : Fin p, (if (φ b).val < T then 1 else 0) :=
          Finset.sum_congr rfl fun b _ => by rw [hval b]
      _ = ∑ u : Fin p, (if u.val < T then 1 else 0) :=
          Fintype.sum_equiv φ _ _ (fun _ => rfl)
      _ = (Finset.univ.filter fun u : Fin p => u.val < T).card := by
          rw [Finset.card_filter]
      _ = T := by
          have hbij : (Finset.univ.filter fun u : Fin p => u.val < T) =
              (Finset.range T).attach.map
                ⟨fun k => ⟨k.1, lt_of_lt_of_le (Finset.mem_range.mp k.2) hTp⟩,
                 fun k₁ k₂ h => Subtype.ext (by simpa using congrArg Fin.val h)⟩ := by
            ext u
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
              Finset.mem_attach, Function.Embedding.coeFn_mk, true_and]
            constructor
            · intro hu
              exact ⟨⟨u.val, Finset.mem_range.mpr hu⟩, Fin.ext rfl⟩
            · rintro ⟨⟨k, hk⟩, hku⟩
              rw [← hku]
              exact Finset.mem_range.mp hk
          rw [hbij, Finset.card_map, Finset.card_attach, Finset.card_range]
  simp_rw [hinner]
  simp

private lemma affine_hash_2pt_card {p : ℕ} [Fact p.Prime] {T : ℕ} (hTp : T ≤ p)
    {x₁ x₂ : ZMod p} (hne : x₁ ≠ x₂) :
    (Finset.univ.filter fun ab : Fin (p - 1) × Fin p =>
      ((ab.1.val + 1) * x₁.val + ab.2.val) % p < T ∧
      ((ab.1.val + 1) * x₂.val + ab.2.val) % p < T).card = T * (T - 1) := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdiff_ne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  let αOf : Fin (p - 1) → ZMod p := fun a => ((a.val + 1 : ℕ) : ZMod p)
  have hα_ne : ∀ a : Fin (p - 1), αOf a ≠ 0 := by
    intro a h0
    have hdvd : p ∣ a.val + 1 := (ZMod.natCast_eq_zero_iff (a.val + 1) p).mp h0
    have hlt : a.val + 1 < p := by omega
    have hpos : 0 < a.val + 1 := Nat.succ_pos _
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  let Φ : Fin (p - 1) × Fin p → {uv : ZMod p × ZMod p // uv.1 ≠ uv.2} := fun ab =>
    ⟨(αOf ab.1 * x₁ + (ab.2.val : ZMod p), αOf ab.1 * x₂ + (ab.2.val : ZMod p)), by
      intro heq
      have hsub : αOf ab.1 * (x₁ - x₂) = 0 := by linear_combination heq
      rcases mul_eq_zero.mp hsub with h1 | h2
      · exact hα_ne ab.1 h1
      · exact hdiff_ne h2⟩
  have hΦ_inj : Function.Injective Φ := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ heq
    have hpair := congrArg Subtype.val heq
    have h1 : αOf a₁ * x₁ + (b₁.val : ZMod p) = αOf a₂ * x₁ + (b₂.val : ZMod p) :=
      congrArg Prod.fst hpair
    have h2 : αOf a₁ * x₂ + (b₁.val : ZMod p) = αOf a₂ * x₂ + (b₂.val : ZMod p) :=
      congrArg Prod.snd hpair
    have ha_eq : αOf a₁ = αOf a₂ := by
      have hmul : (αOf a₁ - αOf a₂) * (x₁ - x₂) = 0 := by linear_combination h1 - h2
      rcases mul_eq_zero.mp hmul with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hdiff_ne
    have ha_val : a₁.val + 1 = a₂.val + 1 := by
      have h1' : (αOf a₁).val = a₁.val + 1 := by
        simp only [αOf, ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
      have h2' : (αOf a₂).val = a₂.val + 1 := by
        simp only [αOf, ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
      rw [← h1', ← h2', ha_eq]
    have ha : a₁ = a₂ := Fin.ext (by omega)
    subst ha
    have hb_z : (b₁.val : ZMod p) = (b₂.val : ZMod p) := by linear_combination h1
    have hb_val : b₁.val = b₂.val := by
      have h1' : ((b₁.val : ZMod p)).val = b₁.val := by
        rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt b₁.isLt
      have h2' : ((b₂.val : ZMod p)).val = b₂.val := by
        rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt b₂.isLt
      rw [← h1', ← h2', hb_z]
    exact Prod.ext rfl (Fin.ext hb_val)
  have hΦ_surj : Function.Surjective Φ := by
    rintro ⟨⟨u, v⟩, huv⟩
    have hαz_ne : (u - v) * (x₁ - x₂)⁻¹ ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr huv) (inv_ne_zero hdiff_ne)
    let αz := (u - v) * (x₁ - x₂)⁻¹
    have hαz_pos : 0 < αz.val := by
      by_contra h0
      have hv0 : αz.val = 0 := by omega
      exact hαz_ne ((ZMod.val_eq_zero αz).mp hv0)
    have hαz_lt : αz.val < p := ZMod.val_lt αz
    let a : Fin (p - 1) := ⟨αz.val - 1, by omega⟩
    have ha_eq : αOf a = αz := by
      simp only [αOf, a]
      rw [Nat.sub_add_cancel hαz_pos, ZMod.natCast_zmod_val]
    let βz := u - αz * x₁
    let b : Fin p := ⟨βz.val, ZMod.val_lt βz⟩
    refine ⟨(a, b), Subtype.ext ?_⟩
    simp only [Φ, ha_eq, b, ZMod.natCast_zmod_val]
    refine Prod.ext ?_ ?_
    · simp [βz]
    · simp only [βz, αz]
      have hmul : (u - v) * (x₁ - x₂)⁻¹ * (x₁ - x₂) = u - v := by
        rw [mul_assoc, inv_mul_cancel₀ hdiff_ne, mul_one]
      linear_combination -hmul
  let eΦ : (Fin (p - 1) × Fin p) ≃ {uv : ZMod p × ZMod p // uv.1 ≠ uv.2} :=
    Equiv.ofBijective Φ ⟨hΦ_inj, hΦ_surj⟩
  have hpred : ∀ ab : Fin (p - 1) × Fin p,
      (((ab.1.val + 1) * x₁.val + ab.2.val) % p < T ∧
       ((ab.1.val + 1) * x₂.val + ab.2.val) % p < T) ↔
      ((eΦ ab).1.1.val < T ∧ (eΦ ab).1.2.val < T) := by
    intro ab
    change _ ↔ (αOf ab.1 * x₁ + (ab.2.val : ZMod p)).val < T ∧
               (αOf ab.1 * x₂ + (ab.2.val : ZMod p)).val < T
    rw [zmod_affine_val_eq ab.1 ab.2 x₁, zmod_affine_val_eq ab.1 ab.2 x₂]
  have hcard1 :
      (Finset.univ.filter fun ab : Fin (p - 1) × Fin p =>
        ((ab.1.val + 1) * x₁.val + ab.2.val) % p < T ∧
        ((ab.1.val + 1) * x₂.val + ab.2.val) % p < T).card =
      (Finset.univ.filter fun uv : {uv : ZMod p × ZMod p // uv.1 ≠ uv.2} =>
        uv.1.1.val < T ∧ uv.1.2.val < T).card := by
    rw [Finset.card_filter, Finset.card_filter]
    refine Fintype.sum_equiv eΦ _ _ fun ab => ?_
    simp [hpred ab]
  rw [hcard1]
  let S : Finset (ZMod p) := Finset.univ.filter fun u : ZMod p => u.val < T
  have hScard : S.card = T := by
    let emb : {k : ℕ // k ∈ Finset.range T} ↪ ZMod p :=
      ⟨fun k => (k.1 : ZMod p), fun k₁ k₂ h => by
        apply Subtype.ext
        have h1 : ((k₁.1 : ZMod p)).val = k₁.1 := by
          rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp k₁.2) hTp)
        have h2 : ((k₂.1 : ZMod p)).val = k₂.1 := by
          rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp k₂.2) hTp)
        rw [← h1, ← h2]
        exact congrArg ZMod.val h⟩
    have hbij : S = (Finset.range T).attach.map emb := by
      ext u
      simp only [S, emb, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_attach, true_and]
      constructor
      · intro hu
        exact ⟨⟨u.val, Finset.mem_range.mpr hu⟩, ZMod.natCast_zmod_val u⟩
      · rintro ⟨⟨k, hk⟩, rfl⟩
        change ((k : ZMod p)).val < T
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hk) hTp)]
        exact Finset.mem_range.mp hk
    rw [hbij, Finset.card_map, Finset.card_attach, Finset.card_range]
  have hcard2 :
      (Finset.univ.filter fun uv : {uv : ZMod p × ZMod p // uv.1 ≠ uv.2} =>
        uv.1.1.val < T ∧ uv.1.2.val < T).card =
      (S.offDiag).card := by
    refine Finset.card_bij (fun uv _ => uv.1) ?_ ?_ ?_
    · intro uv huv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huv
      simp only [Finset.mem_offDiag, S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨huv.1, huv.2, uv.2⟩
    · intro uv₁ _ uv₂ _ h
      exact Subtype.ext h
    · intro xy hxy
      simp only [Finset.mem_offDiag, S, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
      exact ⟨⟨xy, hxy.2.2⟩, by simp [hxy.1, hxy.2.1], rfl⟩
  rw [hcard2, Finset.offDiag_card, hScard]
  cases T with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel]
    have : (k + 1) * (k + 1) - (k + 1) = (k + 1) * k := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
    exact this

private lemma pair_prob_le_sq {p T : ℕ} (hp : 2 ≤ p) (hTp : T ≤ p) :
    ((T * (T - 1) : ℕ) : ℝ) / (((p - 1) * p : ℕ) : ℝ) ≤ ((T : ℝ) / (p : ℝ)) ^ 2 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpm1_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p - 1)
  have hdenom_pos : (0 : ℝ) < (((p - 1) * p : ℕ) : ℝ) := by push_cast; positivity
  rw [div_pow, div_le_div_iff₀ hdenom_pos (by positivity)]
  have hnat : T * (T - 1) * (p * p) ≤ T * T * ((p - 1) * p) := by
    cases T with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      have h1 : k * p ≤ (k + 1) * (p - 1) := by
        have hpm1 : p = (p - 1) + 1 := by omega
        calc k * p = k * ((p - 1) + 1) := by rw [← hpm1]
          _ = k * (p - 1) + k := by ring
          _ ≤ k * (p - 1) + (p - 1) := by omega
          _ = (k + 1) * (p - 1) := by ring
      calc (k + 1) * k * (p * p) = (k + 1) * p * (k * p) := by ring
        _ ≤ (k + 1) * p * ((k + 1) * (p - 1)) := Nat.mul_le_mul_left _ h1
        _ = (k + 1) * (k + 1) * ((p - 1) * p) := by ring
  have hreal : ((T * (T - 1) * (p * p) : ℕ) : ℝ) ≤ ((T * T * ((p - 1) * p) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hreal ⊢
  nlinarith

/-! ### Part 3: 2-torsion bounds for `E(F_p)` and `F_p^*` -/

private lemma ec_two_torsion_card_le {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] :
    letI := ecPointFintype E
    (Finset.univ.filter fun P : E.toAffine.Point => P + P = 0).card ≤ 4 := by
  let _ := ecPointFintype E
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    exact absurd (Nat.le_of_dvd (by decide) hd) (by omega)
  have h4ne : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2ne h2ne
  let f : Polynomial (ZMod p) :=
    Polynomial.C (4 : ZMod p) * Polynomial.X ^ 3 +
    Polynomial.C (4 * E.a₂ + E.a₁ ^ 2) * Polynomial.X ^ 2 +
    Polynomial.C (4 * E.a₄ + 2 * E.a₁ * E.a₃) * Polynomial.X +
    Polynomial.C (4 * E.a₆ + E.a₃ ^ 2)
  have hf_coeff3 : f.coeff 3 = 4 := by
    simp only [f, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have hf_ne : f ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hf_coeff3
    exact h4ne hf_coeff3.symm
  have hf_deg : f.natDegree ≤ 3 := by
    have hd1 : (Polynomial.C (4 : ZMod p) * Polynomial.X ^ 3).natDegree ≤ 3 :=
      le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
    have hd2 : (Polynomial.C (4 * E.a₂ + E.a₁ ^ 2) * Polynomial.X ^ 2).natDegree ≤ 3 :=
      le_trans (Polynomial.natDegree_C_mul_le _ _) (le_trans (Polynomial.natDegree_X_pow_le 2) (by omega))
    have hd3 : (Polynomial.C (4 * E.a₄ + 2 * E.a₁ * E.a₃) * Polynomial.X).natDegree ≤ 3 :=
      le_trans (Polynomial.natDegree_C_mul_le _ _) (le_trans Polynomial.natDegree_X_le (by omega))
    have hd4 : (Polynomial.C (4 * E.a₆ + E.a₃ ^ 2)).natDegree ≤ 3 := by
      rw [Polynomial.natDegree_C]; omega
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ hd4)
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ hd3)
    exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hd1 hd2)
  let S : Finset E.toAffine.Point := Finset.univ.filter fun P : E.toAffine.Point => P + P = 0
  let Saff : Finset E.toAffine.Point := S.erase 0
  have hS_le : S.card ≤ Saff.card + 1 := by
    change S.card ≤ (S.erase 0).card + 1
    by_cases h0 : (0 : E.toAffine.Point) ∈ S
    · have := Finset.card_erase_add_one h0
      omega
    · rw [Finset.erase_eq_of_notMem h0]
      omega
  have hSaff_le : Saff.card ≤ f.roots.toFinset.card := by
    refine Finset.card_le_card_of_injOn
      (fun P => match P with | .zero => 0 | .some x _ _ => x) ?_ ?_
    · intro P hP
      simp only [Saff, S, Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
        Finset.mem_univ, true_and] at hP
      obtain ⟨hP0, hPP⟩ := hP
      cases P with
      | zero => exact absurd rfl hP0
      | some x y h =>
        have hneg : WeierstrassCurve.Affine.Point.some x y h =
            -(WeierstrassCurve.Affine.Point.some x y h) := eq_neg_of_add_eq_zero_left hPP
        rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at hneg
        have hy : y = -y - E.a₁ * x - E.a₃ := hneg.2
        have h2y : 2 * y = -(E.a₁ * x + E.a₃) := by linear_combination hy
        have heq : y ^ 2 + E.a₁ * x * y + E.a₃ * y =
            x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
          have := (E.toAffine.equation_iff x y).mp h.1
          simpa using this
        have hroot : f.eval x = 0 := by
          simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_pow, Polynomial.eval_X]
          linear_combination -4 * heq + (2 * y + E.a₁ * x + E.a₃) * h2y
        rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hf_ne, Polynomial.IsRoot]
        exact hroot
    · intro P₁ hP₁ P₂ hP₂ hxeq
      simp only [Saff, S, Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
        Finset.mem_univ, true_and] at hP₁ hP₂
      cases P₁ with
      | zero => exact absurd rfl hP₁.1
      | some x₁ y₁ h₁ =>
        cases P₂ with
        | zero => exact absurd rfl hP₂.1
        | some x₂ y₂ h₂ =>
          dsimp only at hxeq
          subst hxeq
          have hneg1 : WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ =
              -(WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) := eq_neg_of_add_eq_zero_left hP₁.2
          have hneg2 : WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ =
              -(WeierstrassCurve.Affine.Point.some x₁ y₂ h₂) := eq_neg_of_add_eq_zero_left hP₂.2
          rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at hneg1 hneg2
          have hy1 : y₁ = -y₁ - E.a₁ * x₁ - E.a₃ := hneg1.2
          have hy2 : y₂ = -y₂ - E.a₁ * x₁ - E.a₃ := hneg2.2
          have h2y1 : 2 * y₁ = -(E.a₁ * x₁ + E.a₃) := by linear_combination hy1
          have h2y2 : 2 * y₂ = -(E.a₁ * x₁ + E.a₃) := by linear_combination hy2
          have hy_eq : y₁ = y₂ := by
            have hmul : (2 : ZMod p) * (y₁ - y₂) = 0 := by linear_combination h2y1 - h2y2
            rcases mul_eq_zero.mp hmul with h | h
            · exact absurd h h2ne
            · exact sub_eq_zero.mp h
          subst hy_eq
          rfl
  have hroots_le : f.roots.toFinset.card ≤ 3 := by
    calc f.roots.toFinset.card ≤ f.roots.card := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ ≤ 3 := hf_deg
  change S.card ≤ 4
  omega

private lemma fp_two_torsion_card_le {p : ℕ} [Fact p.Prime] :
    (Finset.univ.filter fun a : Additive (ZMod p)ˣ => a + a = 0).card ≤ 4 := by
  let S := Finset.univ.filter fun a : Additive (ZMod p)ˣ => a + a = 0
  have hsub : S ⊆ ({Additive.ofMul (1 : (ZMod p)ˣ), Additive.ofMul (-1 : (ZMod p)ˣ)} : Finset (Additive (ZMod p)ˣ)) := by
    intro a ha
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    let u : (ZMod p)ˣ := Additive.toMul a
    have hu : u * u = 1 := ha
    have hv : ((u : ZMod p) - 1) * ((u : ZMod p) + 1) = 0 := by
      have hval : (u : ZMod p) * (u : ZMod p) = 1 := by
        simpa using congrArg (Units.val : (ZMod p)ˣ → ZMod p) hu
      linear_combination hval
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases mul_eq_zero.mp hv with h1 | h2
    · left
      have : (u : ZMod p) = 1 := sub_eq_zero.mp h1
      have : u = 1 := Units.ext this
      simpa [u] using congrArg Additive.ofMul this
    · right
      have : (u : ZMod p) = -1 := eq_neg_of_add_eq_zero_left h2
      have : u = -1 := Units.ext this
      simpa [u] using congrArg Additive.ofMul this
  calc S.card ≤ ({Additive.ofMul (1 : (ZMod p)ˣ), Additive.ofMul (-1 : (ZMod p)ˣ)} : Finset _).card :=
        Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two
    _ ≤ 4 := by decide

/-! ### Part 4: Modular abstract moment and collision-energy bounds -/

private lemma prod_avg_eq {Seed₁ : Type*} [Fintype Seed₁] {m : ℕ} (φ : Fin m → Seed₁ → ℝ) :
    (∑ S : Fin m → Seed₁, ∏ i : Fin m, φ i (S i)) / (Fintype.card (Fin m → Seed₁) : ℝ) =
    ∏ i : Fin m, (∑ s : Seed₁, φ i s) / (Fintype.card Seed₁ : ℝ) := by
  have hSm : (Fintype.card (Fin m → Seed₁) : ℝ) =
      ∏ _i : Fin m, (Fintype.card Seed₁ : ℝ) := by
    simp [Fintype.card_pi]
  rw [hSm, ← Fintype.prod_sum, ← Finset.prod_div_distrib]

private lemma avg_productSize_var_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {Seed₁ : Type*} [Fintype Seed₁] [Nonempty Seed₁]
    (Ω : Finset G) (m : ℕ) (θ : ℝ) (mem : Seed₁ → G → Bool)
    (hθ_pos : 0 < θ) (hΩ_pos : 0 < Ω.card)
    (hΩ : ∀ s g, mem s g = true → g ∈ Ω)
    (h1pt : ∀ A ∈ Ω,
      ((Finset.univ.filter fun s : Seed₁ => mem s A = true).card : ℝ) /
        (Fintype.card Seed₁ : ℝ) = θ)
    (h2pt : ∀ A ∈ Ω, ∀ B ∈ Ω, B ≠ A → B ≠ -A →
      ((Finset.univ.filter fun s : Seed₁ => mem s A = true ∧ mem s B = true).card : ℝ) /
        (Fintype.card Seed₁ : ℝ) ≤ θ ^ 2) :
    let qblk := (Ω.card : ℝ) * θ
    let μ := qblk ^ m
    let F : (Fin m → Seed₁) → Fin m → Finset G :=
      fun S i => Finset.univ.filter fun g => mem (S i) g = true
    (∑ S : Fin m → Seed₁, ((productSize (F S) : ℝ) - μ) ^ 2) /
      (Fintype.card (Fin m → Seed₁) : ℝ) ≤ μ ^ 2 * ((1 + 2 / qblk) ^ m - 1) := by
  dsimp only
  set qblk : ℝ := (Ω.card : ℝ) * θ
  set μ : ℝ := qblk ^ m
  set F : (Fin m → Seed₁) → Fin m → Finset G :=
    fun S i => Finset.univ.filter fun g => mem (S i) g = true
  have hS1_pos : (0 : ℝ) < (Fintype.card Seed₁ : ℝ) := by exact_mod_cast Fintype.card_pos (α := Seed₁)
  have hSm_pos : (0 : ℝ) < (Fintype.card (Fin m → Seed₁) : ℝ) := by
    rw [Fintype.card_pi]; simp; positivity
  have hqblk_pos : 0 < qblk := by
    have : (0 : ℝ) < (Ω.card : ℝ) := by exact_mod_cast hΩ_pos
    positivity
  let p2 : G → G → ℝ := fun A B =>
    ((Finset.univ.filter fun s : Seed₁ => mem s A = true ∧ mem s B = true).card : ℝ) /
      (Fintype.card Seed₁ : ℝ)
  have hp2_le_θ : ∀ A ∈ Ω, ∀ B : G, p2 A B ≤ θ := by
    intro A hA B
    rw [← h1pt A hA]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hS1_pos)
    exact_mod_cast Finset.card_le_card fun s hs => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact hs.1
  have hE1 : (∑ s : Seed₁, ((Finset.univ.filter fun g : G => mem s g = true).card : ℝ)) /
      (Fintype.card Seed₁ : ℝ) = qblk := by
    have hcard_eq : ∀ s : Seed₁,
        ((Finset.univ.filter fun g : G => mem s g = true).card : ℝ) =
        ∑ A ∈ Ω, if mem s A = true then (1 : ℝ) else 0 := by
      intro s
      have hsub : (Finset.univ.filter fun g : G => mem s g = true) =
          Ω.filter (fun g => mem s g = true) := by
        ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨hΩ s g h, h⟩, fun h => h.2⟩
      rw [hsub, Finset.card_filter]; push_cast; rfl
    simp_rw [hcard_eq]
    rw [Finset.sum_comm, Finset.sum_div]
    have hterm : ∀ A ∈ Ω,
        (∑ s : Seed₁, (if mem s A = true then (1 : ℝ) else 0)) / (Fintype.card Seed₁ : ℝ) = θ := by
      intro A hA
      have hsum : (∑ s : Seed₁, (if mem s A = true then (1 : ℝ) else 0)) =
          ((Finset.univ.filter fun s : Seed₁ => mem s A = true).card : ℝ) := by
        rw [Finset.card_filter]; push_cast; rfl
      rw [hsum, h1pt A hA]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hE2 : (∑ s : Seed₁, (((Finset.univ.filter fun g : G => mem s g = true).card : ℝ) ^ 2)) /
      (Fintype.card Seed₁ : ℝ) ≤ qblk ^ 2 * (1 + 2 / qblk) := by
    have hcard_sq : ∀ s : Seed₁,
        ((Finset.univ.filter fun g : G => mem s g = true).card : ℝ) ^ 2 =
        ∑ A ∈ Ω, ∑ B ∈ Ω, if (mem s A = true ∧ mem s B = true) then (1 : ℝ) else 0 := by
      intro s
      have hsub : (Finset.univ.filter fun g : G => mem s g = true) =
          Ω.filter (fun g => mem s g = true) := by
        ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨hΩ s g h, h⟩, fun h => h.2⟩
      rw [hsub, sq, Finset.card_filter]; push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun A _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun B _ => ?_
      by_cases hA : mem s A = true <;> by_cases hB : mem s B = true <;> simp [hA, hB]
    simp_rw [hcard_sq]
    rw [Finset.sum_comm, Finset.sum_div]
    have hA_bound : ∀ A ∈ Ω,
        (∑ s : Seed₁, ∑ B ∈ Ω, if (mem s A = true ∧ mem s B = true) then (1 : ℝ) else 0) /
          (Fintype.card Seed₁ : ℝ) ≤ 2 * θ + (Ω.card : ℝ) * θ ^ 2 := by
      intro A hA
      rw [Finset.sum_comm, Finset.sum_div]
      have hterm : ∀ B ∈ Ω,
          (∑ s : Seed₁, if (mem s A = true ∧ mem s B = true) then (1 : ℝ) else 0) /
            (Fintype.card Seed₁ : ℝ) = p2 A B := by
        intro B _; dsimp [p2]; congr 1; rw [Finset.card_filter]; push_cast; rfl
      rw [Finset.sum_congr rfl hterm]
      have hle : ∑ B ∈ Ω, p2 A B ≤
          ∑ B ∈ Ω, ((if B = A ∨ B = -A then θ else 0) + θ ^ 2) := by
        refine Finset.sum_le_sum fun B hB => ?_
        by_cases hBA : B = A ∨ B = -A
        · rw [if_pos hBA]; have := hp2_le_θ A hA B; nlinarith [sq_nonneg θ]
        · rw [if_neg hBA, zero_add]; push Not at hBA; exact h2pt A hA B hB hBA.1 hBA.2
      refine le_trans hle ?_
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hspec : ∑ B ∈ Ω, (if B = A ∨ B = -A then θ else 0) ≤ 2 * θ := by
        have h1 : ∑ B ∈ Ω, (if B = A ∨ B = -A then θ else 0) =
            ((Ω.filter fun B => B = A ∨ B = -A).card : ℝ) * θ := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [h1]
        have hsub : (Ω.filter fun B => B = A ∨ B = -A) ⊆ ({A, -A} : Finset G) := by
          intro B hB; simp only [Finset.mem_filter] at hB
          simp only [Finset.mem_insert, Finset.mem_singleton]; exact hB.2
        have hcard : (Ω.filter fun B => B = A ∨ B = -A).card ≤ 2 :=
          le_trans (Finset.card_le_card hsub) Finset.card_le_two
        have hcardR : ((Ω.filter fun B => B = A ∨ B = -A).card : ℝ) ≤ 2 := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hcardR (le_of_lt hθ_pos)
      linarith
    calc ∑ A ∈ Ω, (∑ s : Seed₁, ∑ B ∈ Ω,
            if (mem s A = true ∧ mem s B = true) then (1 : ℝ) else 0) / (Fintype.card Seed₁ : ℝ)
        ≤ ∑ _A ∈ Ω, (2 * θ + (Ω.card : ℝ) * θ ^ 2) := Finset.sum_le_sum hA_bound
      _ = (Ω.card : ℝ) * (2 * θ + (Ω.card : ℝ) * θ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = qblk ^ 2 * (1 + 2 / qblk) := by
          have hqne : qblk ≠ 0 := ne_of_gt hqblk_pos
          field_simp [hqne]
          dsimp [qblk]
          ring
  have hEW : (∑ S : Fin m → Seed₁, (productSize (F S) : ℝ)) /
      (Fintype.card (Fin m → Seed₁) : ℝ) = μ := by
    have hprod_eq : ∀ S : Fin m → Seed₁,
        (productSize (F S) : ℝ) = ∏ i : Fin m, ((F S i).card : ℝ) := by
      intro S; unfold productSize; push_cast; rfl
    simp_rw [hprod_eq]
    rw [prod_avg_eq (fun _ s => ((Finset.univ.filter fun g : G => mem s g = true).card : ℝ))]
    simp_rw [hE1]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hEW2 : (∑ S : Fin m → Seed₁, (productSize (F S) : ℝ) ^ 2) /
      (Fintype.card (Fin m → Seed₁) : ℝ) ≤ μ ^ 2 * (1 + 2 / qblk) ^ m := by
    have hprod_eq : ∀ S : Fin m → Seed₁,
        (productSize (F S) : ℝ) ^ 2 = ∏ i : Fin m, ((F S i).card : ℝ) ^ 2 := by
      intro S; unfold productSize; push_cast; rw [Finset.prod_pow]
    simp_rw [hprod_eq]
    rw [prod_avg_eq (fun _ s => ((Finset.univ.filter fun g : G => mem s g = true).card : ℝ) ^ 2)]
    have hnn : ∀ _i : Fin m,
        0 ≤ (∑ s : Seed₁, ((Finset.univ.filter fun g : G => mem s g = true).card : ℝ) ^ 2) /
            (Fintype.card Seed₁ : ℝ) := fun _ =>
      div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (le_of_lt hS1_pos)
    calc ∏ _i : Fin m, (∑ s : Seed₁, ((Finset.univ.filter fun g : G => mem s g = true).card : ℝ) ^ 2) /
            (Fintype.card Seed₁ : ℝ)
        ≤ ∏ _i : Fin m, (qblk ^ 2 * (1 + 2 / qblk)) :=
          Finset.prod_le_prod (fun i _ => hnn i) (fun _ _ => hE2)
      _ = (qblk ^ 2 * (1 + 2 / qblk)) ^ m := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = μ ^ 2 * (1 + 2 / qblk) ^ m := by
          rw [mul_pow, ← pow_mul, mul_comm 2 m, pow_mul]
  have hexp : ∀ S : Fin m → Seed₁,
      ((productSize (F S) : ℝ) - μ) ^ 2 =
      (productSize (F S) : ℝ) ^ 2 - 2 * μ * (productSize (F S) : ℝ) + μ ^ 2 := fun S => by ring
  change (∑ S : Fin m → Seed₁, ((productSize (F S) : ℝ) - μ) ^ 2) /
      (Fintype.card (Fin m → Seed₁) : ℝ) ≤ μ ^ 2 * ((1 + 2 / qblk) ^ m - 1)
  simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    add_div, sub_div, mul_div_assoc]
  rw [hEW]
  have hconst : (∑ _S : Fin m → Seed₁, μ ^ 2) / (Fintype.card (Fin m → Seed₁) : ℝ) = μ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ (ne_of_gt hSm_pos)]
  rw [hconst]
  linarith

private lemma avg_collisionEnergy_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {Seed₁ : Type*} [Fintype Seed₁] [Nonempty Seed₁]
    (Ω : Finset G) (m : ℕ) (θ : ℝ) (mem : Seed₁ → G → Bool)
    (hm : 1 ≤ m) (hΩ_pos : 0 < Ω.card) (hθ_pos : 0 < θ)
    (h2tors : (Finset.univ.filter fun g : G => g + g = 0).card ≤ 4)
    (hΩ : ∀ s g, mem s g = true → g ∈ Ω)
    (h1pt : ∀ A ∈ Ω,
      ((Finset.univ.filter fun s : Seed₁ => mem s A = true).card : ℝ) /
        (Fintype.card Seed₁ : ℝ) = θ)
    (h2pt : ∀ A ∈ Ω, ∀ B ∈ Ω, B ≠ A → B ≠ -A →
      ((Finset.univ.filter fun s : Seed₁ => mem s A = true ∧ mem s B = true).card : ℝ) /
        (Fintype.card Seed₁ : ℝ) ≤ θ ^ 2) :
    let qblk := (Ω.card : ℝ) * θ
    let μ := qblk ^ m
    let F : (Fin m → Seed₁) → Fin m → Finset G :=
      fun S i => Finset.univ.filter fun g => mem (S i) g = true
    (∑ S : Fin m → Seed₁, (collisionEnergyAdd (F S) : ℝ)) /
      (Fintype.card (Fin m → Seed₁) : ℝ) ≤
    μ + (4 * (2 : ℝ) ^ m * μ) / (Ω.card : ℝ) + (μ ^ 2 / (Ω.card : ℝ)) * (1 + 2 / qblk) ^ m := by
  dsimp only
  set n : ℕ := Ω.card
  set qblk : ℝ := (n : ℝ) * θ
  set μ : ℝ := qblk ^ m
  set F : (Fin m → Seed₁) → Fin m → Finset G :=
    fun S i => Finset.univ.filter fun g => mem (S i) g = true
  have hS1_pos : (0 : ℝ) < (Fintype.card Seed₁ : ℝ) := by exact_mod_cast Fintype.card_pos (α := Seed₁)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hΩ_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hqblk_pos : 0 < qblk := mul_pos hn_pos hθ_pos
  let p2 : G → G → ℝ := fun A B =>
    ((Finset.univ.filter fun s : Seed₁ => mem s A = true ∧ mem s B = true).card : ℝ) /
      (Fintype.card Seed₁ : ℝ)
  have hp2_le_θ : ∀ A ∈ Ω, ∀ B : G, p2 A B ≤ θ := by
    intro A hA B
    rw [← h1pt A hA]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hS1_pos)
    exact_mod_cast Finset.card_le_card fun s hs => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact hs.1
  have hp2_nn : ∀ A B : G, 0 ≤ p2 A B := fun A B => by dsimp [p2]; positivity
  let Ωm : Finset (Fin m → G) := Fintype.piFinset (fun _ : Fin m => Ω)
  let Pairs : Finset ((Fin m → G) × (Fin m → G)) :=
    (Ωm ×ˢ Ωm).filter fun AA' => ∑ i : Fin m, AA'.1 i = ∑ i : Fin m, AA'.2 i
  have hC_eq : ∀ S : Fin m → Seed₁,
      (collisionEnergyAdd (F S) : ℝ) =
      ∑ AA' ∈ Pairs, ∏ i : Fin m,
        if (mem (S i) (AA'.1 i) = true ∧ mem (S i) (AA'.2 i) = true) then (1 : ℝ) else 0 := by
    intro S
    unfold collisionEnergyAdd repCountAdd
    have hsq : ∀ g : G,
        (((Fintype.piFinset (F S)).filter fun A => ∑ i : Fin m, A i = g).card : ℝ) ^ 2 =
        (((Fintype.piFinset (F S) ×ˢ Fintype.piFinset (F S)).filter
          fun AA' => ∑ i : Fin m, AA'.1 i = g ∧ ∑ i : Fin m, AA'.2 i = g).card : ℝ) := by
      intro g
      norm_cast
      rw [sq, ← Finset.card_product]
      congr 1; ext ⟨A, A'⟩; simp only [Finset.mem_product, Finset.mem_filter]; tauto
    push_cast
    simp_rw [hsq]
    have hpart :
        (∑ g : G, ((Fintype.piFinset (F S) ×ˢ Fintype.piFinset (F S)).filter
          fun AA' => ∑ i : Fin m, AA'.1 i = g ∧ ∑ i : Fin m, AA'.2 i = g).card) =
        ((Fintype.piFinset (F S) ×ˢ Fintype.piFinset (F S)).filter
          fun AA' => ∑ i : Fin m, AA'.1 i = ∑ i : Fin m, AA'.2 i).card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun AA' _ => ?_
      by_cases heq : ∑ i : Fin m, AA'.1 i = ∑ i : Fin m, AA'.2 i
      · rw [if_pos heq, Finset.sum_eq_single (∑ i : Fin m, AA'.1 i)]
        · simp [heq]
        · intro g _ hg; simp [Ne.symm hg]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg heq]
        refine Finset.sum_eq_zero fun g _ => ?_
        have hnot : ¬ (∑ i : Fin m, AA'.1 i = g ∧ ∑ i : Fin m, AA'.2 i = g) := by
          rintro ⟨h1, h2⟩; exact heq (h1.trans h2.symm)
        simp [hnot]
    have hpartR :
        (∑ g : G, (((Fintype.piFinset (F S) ×ˢ Fintype.piFinset (F S)).filter
          fun AA' => ∑ i : Fin m, AA'.1 i = g ∧ ∑ i : Fin m, AA'.2 i = g).card : ℝ)) =
        (((Fintype.piFinset (F S) ×ˢ Fintype.piFinset (F S)).filter
          fun AA' => ∑ i : Fin m, AA'.1 i = ∑ i : Fin m, AA'.2 i).card : ℝ) := by
      exact_mod_cast hpart
    rw [hpartR]
    have hsub : ((Fintype.piFinset (F S) ×ˢ Fintype.piFinset (F S)).filter
          fun AA' => ∑ i : Fin m, AA'.1 i = ∑ i : Fin m, AA'.2 i) =
        Pairs.filter fun AA' => ∀ i : Fin m, mem (S i) (AA'.1 i) = true ∧ mem (S i) (AA'.2 i) = true := by
      ext ⟨A, A'⟩
      simp only [Pairs, Ωm, F, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hA, hA'⟩, hsum⟩
        exact ⟨⟨⟨fun i => hΩ (S i) (A i) (hA i), fun i => hΩ (S i) (A' i) (hA' i)⟩, hsum⟩,
          fun i => ⟨hA i, hA' i⟩⟩
      · rintro ⟨⟨_, hsum⟩, hmem⟩
        exact ⟨⟨fun i => (hmem i).1, fun i => (hmem i).2⟩, hsum⟩
    rw [hsub, Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl fun AA' _ => ?_
    by_cases h : ∀ i : Fin m, mem (S i) (AA'.1 i) = true ∧ mem (S i) (AA'.2 i) = true
    · rw [if_pos h]; symm; exact Finset.prod_eq_one fun i _ => by rw [if_pos (h i)]
    · rw [if_neg h]; obtain ⟨i, hi⟩ := not_forall.mp h
      symm; exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])
  have hEC_sum :
      (∑ S : Fin m → Seed₁, (collisionEnergyAdd (F S) : ℝ)) /
        (Fintype.card (Fin m → Seed₁) : ℝ) =
      ∑ AA' ∈ Pairs, ∏ i : Fin m, p2 (AA'.1 i) (AA'.2 i) := by
    simp_rw [hC_eq]
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun AA' _ => ?_
    rw [prod_avg_eq (fun i s =>
      if (mem s (AA'.1 i) = true ∧ mem s (AA'.2 i) = true) then (1 : ℝ) else 0)]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp [p2]; congr 1; rw [Finset.card_filter]; push_cast; rfl
  let tagOf : (Fin m → G) × (Fin m → G) → Fin m → Fin 3 := fun AA' i =>
    if AA'.2 i = AA'.1 i then 0
    else if AA'.2 i = -(AA'.1 i) then 1
    else 2
  let Jof : (Fin m → Fin 3) → Finset (Fin m) := fun t => Finset.univ.filter fun i => t i ≠ 2
  have hEC_tag :
      ∑ AA' ∈ Pairs, ∏ i : Fin m, p2 (AA'.1 i) (AA'.2 i) ≤
      ∑ t : Fin m → Fin 3,
        ((Pairs.filter fun AA' => tagOf AA' = t).card : ℝ) * θ ^ (2 * m - (Jof t).card) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := tagOf) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_le_sum fun t _ => ?_
    have hle : ∀ AA' ∈ Pairs.filter (fun AA' => tagOf AA' = t),
        ∏ i : Fin m, p2 (AA'.1 i) (AA'.2 i) ≤ θ ^ (2 * m - (Jof t).card) := by
      intro AA' hAA'
      simp only [Finset.mem_filter, Pairs, Ωm, Finset.mem_product, Fintype.mem_piFinset] at hAA'
      obtain ⟨⟨⟨hA, hA'⟩, _⟩, htag⟩ := hAA'
      have hstep : ∏ i : Fin m, p2 (AA'.1 i) (AA'.2 i) ≤
          ∏ i : Fin m, if i ∈ Jof t then θ else θ ^ 2 := by
        refine Finset.prod_le_prod (fun i _ => hp2_nn _ _) fun i _ => ?_
        have hti : tagOf AA' i = t i := congrFun htag i
        by_cases hi : i ∈ Jof t
        · rw [if_pos hi]; exact hp2_le_θ (AA'.1 i) (hA i) (AA'.2 i)
        · rw [if_neg hi]
          simp only [Jof, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
          rw [hi] at hti
          have hne1 : AA'.2 i ≠ AA'.1 i := by
            intro heq; simp only [tagOf, heq, ↓reduceIte] at hti; exact absurd hti (by decide)
          have hne2 : AA'.2 i ≠ -(AA'.1 i) := by
            intro heq
            simp only [tagOf, heq] at hti
            split_ifs at hti
            · exact absurd hti (by decide)
            · exact absurd hti (by decide)
          exact h2pt (AA'.1 i) (hA i) (AA'.2 i) (hA' i) hne1 hne2
      refine le_trans hstep ?_
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      have hcard_compl : (Finset.univ.filter fun i : Fin m => i ∉ Jof t).card = m - (Jof t).card := by
        have hcompl_eq : (Finset.univ.filter fun i : Fin m => i ∉ Jof t) = (Jof t)ᶜ := by
          ext i; simp
        rw [hcompl_eq, Finset.card_compl, Fintype.card_fin]
      have hcard_in : (Finset.univ.filter fun i : Fin m => i ∈ Jof t).card = (Jof t).card := by
        congr 1; ext i; simp
      rw [hcard_in, hcard_compl, ← pow_mul, ← pow_add]
      have hle_m : (Jof t).card ≤ m := by
        calc (Jof t).card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
          _ = m := Fintype.card_fin m
      exact le_of_eq (congrArg (θ ^ ·) (by omega))
    calc ∑ AA' ∈ Pairs.filter (fun AA' => tagOf AA' = t), ∏ i : Fin m, p2 (AA'.1 i) (AA'.2 i)
        ≤ ∑ _AA' ∈ Pairs.filter (fun AA' => tagOf AA' = t), θ ^ (2 * m - (Jof t).card) :=
          Finset.sum_le_sum hle
      _ = ((Pairs.filter fun AA' => tagOf AA' = t).card : ℝ) * θ ^ (2 * m - (Jof t).card) := by simp
  have hfiber_diag : (Pairs.filter fun AA' => tagOf AA' = (fun _ => 0)).card ≤ n ^ m := by
    let D0 := Pairs.filter fun AA' => tagOf AA' = (fun _ => 0)
    have hinj : Set.InjOn (fun x : (Fin m → G) × (Fin m → G) => x.1) (D0 : Set _) := by
      intro x hx y hy hfst
      simp only [D0, Finset.mem_coe, Finset.mem_filter] at hx hy
      dsimp only at hfst
      refine Prod.ext hfst (funext fun i => ?_)
      have hxi : tagOf x i = 0 := congrFun hx.2 i
      have hyi : tagOf y i = 0 := congrFun hy.2 i
      have hx2 : x.2 i = x.1 i := by
        by_contra hne
        simp only [tagOf] at hxi
        by_cases hneg : x.2 i = -(x.1 i)
        · rw [if_neg hne, if_pos hneg] at hxi; exact absurd hxi (by decide)
        · rw [if_neg hne, if_neg hneg] at hxi; exact absurd hxi (by decide)
      have hy2 : y.2 i = y.1 i := by
        by_contra hne
        simp only [tagOf] at hyi
        by_cases hneg : y.2 i = -(y.1 i)
        · rw [if_neg hne, if_pos hneg] at hyi; exact absurd hyi (by decide)
        · rw [if_neg hne, if_neg hneg] at hyi; exact absurd hyi (by decide)
      rw [hx2, hy2, hfst]
    calc D0.card
        ≤ Ωm.card := Finset.card_le_card_of_injOn (fun x => x.1)
          (fun x hx => by
            simp only [D0, Finset.mem_coe, Finset.mem_filter, Pairs, Finset.mem_product] at hx
            exact hx.1.1.1) hinj
      _ = n ^ m := by simp [Ωm, n]
  have hfiber_full : ∀ t : Fin m → Fin 3, Jof t = Finset.univ → t ≠ (fun _ => 0) →
      (Pairs.filter fun AA' => tagOf AA' = t).card ≤ 4 * n ^ (m - 1) := by
    intro t hJ ht0
    have hex : ∃ i₀ : Fin m, t i₀ = 1 := by
      by_contra hno
      push Not at hno
      apply ht0
      funext i
      have hi : i ∈ Jof t := by rw [hJ]; exact Finset.mem_univ i
      simp only [Jof, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have h1 : (t i).val ≠ 1 := fun hv => hno i (Fin.ext hv)
      have h2 : (t i).val ≠ 2 := fun hv => hi (Fin.ext hv)
      have hlt := (t i).isLt
      exact Fin.ext (by omega)
    obtain ⟨i₀, hi₀⟩ := hex
    let Rest : Finset ({i : Fin m // i ≠ i₀} → G) := Fintype.piFinset (fun _ => Ω)
    let Tors : Finset G := Finset.univ.filter fun g : G => g + g = 0
    let Fset := Pairs.filter fun AA' => tagOf AA' = t
    let proj : (Fin m → G) × (Fin m → G) → ({i : Fin m // i ≠ i₀} → G) := fun AA' j => AA'.1 j.1
    rw [Finset.card_eq_sum_card_fiberwise (f := proj) (s := Fset) (t := Rest) (by
      intro AA' hAA'
      simp only [Fset, Pairs, Ωm, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Fintype.mem_piFinset] at hAA'
      simp only [Rest, Finset.mem_coe, Fintype.mem_piFinset]
      exact fun j => hAA'.1.1.1 j.1)]
    have hfiber_le : ∀ r ∈ Rest, (Fset.filter fun AA' => proj AA' = r).card ≤ 4 := by
      intro r _
      by_cases hne : (Fset.filter fun AA' => proj AA' = r).Nonempty
      · obtain ⟨P0, hP0⟩ := hne
        have hP0' := hP0
        simp only [Finset.mem_filter] at hP0'
        have hdet : ∀ AA' ∈ Fset, ∀ i : Fin m,
            AA'.2 i = if t i = 0 then AA'.1 i else -(AA'.1 i) := by
          intro AA' hAA' i
          simp only [Fset, Finset.mem_filter] at hAA'
          have hti : tagOf AA' i = t i := congrFun hAA'.2 i
          have hne2 : t i ≠ 2 := by
            have hi : i ∈ Jof t := by rw [hJ]; exact Finset.mem_univ i
            simp only [Jof, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact hi
          by_cases h0 : AA'.2 i = AA'.1 i
          · have : t i = 0 := by simp only [tagOf] at hti; rw [if_pos h0] at hti; exact hti.symm
            simp [this, h0]
          · by_cases h1 : AA'.2 i = -(AA'.1 i)
            · have : t i = 1 := by simp only [tagOf] at hti; rw [if_neg h0, if_pos h1] at hti; exact hti.symm
              simp [this, h1]
            · exfalso
              have : t i = 2 := by simp only [tagOf] at hti; rw [if_neg h0, if_neg h1] at hti; exact hti.symm
              exact hne2 this
        have hsub_eq : ∀ AA' ∈ Fset,
            ∑ i : Fin m, (if t i = 0 then (0 : G) else AA'.1 i + AA'.1 i) = 0 := by
          intro AA' hAA'
          have hsum : ∑ i : Fin m, AA'.1 i = ∑ i : Fin m, AA'.2 i := by
            simp only [Fset, Pairs, Finset.mem_filter] at hAA'
            exact hAA'.1.2
          have hdiff : ∑ i : Fin m, (AA'.1 i - AA'.2 i) = 0 := by
            rw [Finset.sum_sub_distrib, hsum, sub_self]
          trans (∑ i : Fin m, (AA'.1 i - AA'.2 i))
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [hdet AA' hAA' i]
            by_cases ht : t i = 0
            · simp [ht]
            · simp [ht, sub_neg_eq_add]
          · exact hdiff
        have hmap_to_tors : ∀ AA' ∈ Fset.filter (fun AA' => proj AA' = r),
            AA'.1 i₀ - P0.1 i₀ ∈ Tors := by
          intro AA' hAA'
          simp only [Finset.mem_filter] at hAA'
          have h1 := hsub_eq AA' hAA'.1
          have h2 := hsub_eq P0 hP0'.1
          have hsame : ∀ i : Fin m, i ≠ i₀ → AA'.1 i = P0.1 i := by
            intro i hi
            have hr1 : proj AA' ⟨i, hi⟩ = r ⟨i, hi⟩ := congrFun hAA'.2 ⟨i, hi⟩
            have hr2 : proj P0 ⟨i, hi⟩ = r ⟨i, hi⟩ := congrFun hP0'.2 ⟨i, hi⟩
            exact hr1.trans hr2.symm
          have hdiff : ∑ i : Fin m,
              ((if t i = 0 then (0 : G) else AA'.1 i + AA'.1 i) -
               (if t i = 0 then (0 : G) else P0.1 i + P0.1 i)) = 0 := by
            rw [Finset.sum_sub_distrib, h1, h2, sub_self]
          rw [Finset.sum_eq_single i₀] at hdiff
          · simp only [hi₀, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hdiff
            simp only [Tors, Finset.mem_filter, Finset.mem_univ, true_and]
            calc (AA'.1 i₀ - P0.1 i₀) + (AA'.1 i₀ - P0.1 i₀)
                = (AA'.1 i₀ + AA'.1 i₀) - (P0.1 i₀ + P0.1 i₀) := by abel
              _ = 0 := hdiff
          · intro i _ hi; rw [hsame i hi, sub_self]
          · intro h; exact absurd (Finset.mem_univ _) h
        have hinj : Set.InjOn (fun AA' : (Fin m → G) × (Fin m → G) => AA'.1 i₀ - P0.1 i₀)
            (↑(Fset.filter (fun AA' => proj AA' = r)) : Set _) := by
          intro x hx y hy hdiff
          simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
          have hi0_eq : x.1 i₀ = y.1 i₀ := sub_left_inj.mp hdiff
          have h1eq : x.1 = y.1 := funext fun i => by
            by_cases hi : i = i₀
            · subst hi; exact hi0_eq
            · have hr1 : proj x ⟨i, hi⟩ = r ⟨i, hi⟩ := congrFun hx.2 ⟨i, hi⟩
              have hr2 : proj y ⟨i, hi⟩ = r ⟨i, hi⟩ := congrFun hy.2 ⟨i, hi⟩
              exact hr1.trans hr2.symm
          refine Prod.ext h1eq (funext fun i => ?_)
          rw [hdet x hx.1 i, hdet y hy.1 i, h1eq]
        exact le_trans (Finset.card_le_card_of_injOn _ (fun x hx => hmap_to_tors x hx) hinj) h2tors
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
    calc ∑ r ∈ Rest, (Fset.filter fun AA' => proj AA' = r).card
        ≤ ∑ _r ∈ Rest, 4 := Finset.sum_le_sum hfiber_le
      _ = Rest.card * 4 := by simp
      _ = 4 * n ^ (m - 1) := by
          have hRcard : Rest.card = n ^ (m - 1) := by
            simp [Rest, Fintype.card_subtype_compl, n]
          rw [hRcard, mul_comm]
  have hfiber_partial : ∀ t : Fin m → Fin 3, Jof t ≠ Finset.univ →
      (Pairs.filter fun AA' => tagOf AA' = t).card ≤ n ^ (2 * m - (Jof t).card - 1) := by
    intro t hJ
    have hex : ∃ i₀ : Fin m, i₀ ∉ Jof t := by
      by_contra hno; push Not at hno; apply hJ; ext i; simp [hno i]
    obtain ⟨i₀, hi₀⟩ := hex
    let Free : Finset (Fin m) := (Jof t)ᶜ.erase i₀
    have hFreecard : Free.card = m - (Jof t).card - 1 := by
      have hi0_in : i₀ ∈ (Jof t)ᶜ := Finset.mem_compl.mpr hi₀
      rw [Finset.card_erase_of_mem hi0_in, Finset.card_compl, Fintype.card_fin]
    let Dom : Finset ((Fin m → G) × ({i : Fin m // i ∈ Free} → G)) :=
      Ωm ×ˢ Fintype.piFinset (fun _ => Ω)
    let proj : (Fin m → G) × (Fin m → G) → (Fin m → G) × ({i : Fin m // i ∈ Free} → G) :=
      fun AA' => (AA'.1, fun j => AA'.2 j.1)
    have hmaps : ∀ AA' ∈ Pairs.filter (fun AA' => tagOf AA' = t), proj AA' ∈ Dom := by
      intro AA' hAA'
      simp only [Pairs, Ωm, Dom, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset] at hAA' ⊢
      exact ⟨hAA'.1.1.1, fun j => hAA'.1.1.2 j.1⟩
    have hinj : Set.InjOn proj (↑(Pairs.filter (fun AA' => tagOf AA' = t)) : Set _) := by
      intro x hx y hy hp
      simp only [Finset.mem_coe, Finset.mem_filter, Pairs] at hx hy
      have h1eq : x.1 = y.1 := (Prod.mk.inj hp).1
      have hfree_eq : ∀ i ∈ Free, x.2 i = y.2 i := fun i hi =>
        congrFun (Prod.mk.inj hp).2 ⟨i, hi⟩
      have hJ_eq : ∀ i ∈ Jof t, x.2 i = y.2 i := by
        intro i hi
        simp only [Jof, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have hxi : tagOf x i = t i := congrFun hx.2 i
        have hyi : tagOf y i = t i := congrFun hy.2 i
        have hdet : ∀ AA' : (Fin m → G) × (Fin m → G), tagOf AA' i = t i →
            AA'.2 i = if t i = 0 then AA'.1 i else -(AA'.1 i) := by
          intro AA' hti
          by_cases h0 : AA'.2 i = AA'.1 i
          · have : t i = 0 := by simp only [tagOf] at hti; rw [if_pos h0] at hti; exact hti.symm
            simp [this, h0]
          · by_cases h1 : AA'.2 i = -(AA'.1 i)
            · have : t i = 1 := by simp only [tagOf] at hti; rw [if_neg h0, if_pos h1] at hti; exact hti.symm
              simp [this, h1]
            · exfalso
              have : t i = 2 := by simp only [tagOf] at hti; rw [if_neg h0, if_neg h1] at hti; exact hti.symm
              exact hi this
        rw [hdet x hxi, hdet y hyi, h1eq]
      have hother_eq : ∀ i : Fin m, i ≠ i₀ → x.2 i = y.2 i := by
        intro i hi
        by_cases hmem : i ∈ Jof t
        · exact hJ_eq i hmem
        · exact hfree_eq i (Finset.mem_erase.mpr ⟨hi, Finset.mem_compl.mpr hmem⟩)
      have hsum_eq : ∑ i : Fin m, x.2 i = ∑ i : Fin m, y.2 i := by
        rw [← hx.1.2, ← hy.1.2, h1eq]
      have haddx := Finset.add_sum_erase Finset.univ (fun i => x.2 i) (Finset.mem_univ i₀)
      have haddy := Finset.add_sum_erase Finset.univ (fun i => y.2 i) (Finset.mem_univ i₀)
      have herase_eq : ∑ i ∈ Finset.univ.erase i₀, x.2 i = ∑ i ∈ Finset.univ.erase i₀, y.2 i :=
        Finset.sum_congr rfl fun i hi => hother_eq i (Finset.ne_of_mem_erase hi)
      have hi0_eq : x.2 i₀ = y.2 i₀ := by
        have h1 : x.2 i₀ + ∑ i ∈ Finset.univ.erase i₀, x.2 i =
            y.2 i₀ + ∑ i ∈ Finset.univ.erase i₀, y.2 i := by
          rw [haddx, haddy, hsum_eq]
        rw [herase_eq] at h1; exact add_right_cancel h1
      refine Prod.ext h1eq (funext fun i => ?_)
      by_cases hi : i = i₀
      · subst hi; exact hi0_eq
      · exact hother_eq i hi
    calc (Pairs.filter fun AA' => tagOf AA' = t).card
        ≤ Dom.card := Finset.card_le_card_of_injOn proj (fun x hx => hmaps x hx) hinj
      _ = n ^ m * n ^ Free.card := by
          simp [Dom, Ωm, n]
      _ = n ^ (2 * m - (Jof t).card - 1) := by
          rw [← pow_add, hFreecard]
          have hJ_lt : (Jof t).card < m := by
            have hss : Jof t ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hJ⟩
            simpa using Finset.card_lt_card hss
          congr 1; omega
  rw [hEC_sum]
  refine le_trans hEC_tag ?_
  have hsplit :
      ∑ t : Fin m → Fin 3,
        ((Pairs.filter fun AA' => tagOf AA' = t).card : ℝ) * θ ^ (2 * m - (Jof t).card) ≤
      ∑ t : Fin m → Fin 3,
        ((if t = (fun _ => 0) then μ else 0) +
         (if Jof t = Finset.univ ∧ t ≠ (fun _ => 0) then (4 : ℝ) * (n : ℝ) ^ (m - 1) * θ ^ m else 0) +
         (if Jof t ≠ Finset.univ then (μ ^ 2 / (n : ℝ)) * (1 / qblk) ^ (Jof t).card else 0)) := by
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases hJ : Jof t = Finset.univ
    · have hJcard : (Jof t).card = m := by rw [hJ]; simp
      have hexp_eq : 2 * m - (Jof t).card = m := by omega
      by_cases ht0 : t = (fun _ => 0)
      · rw [hexp_eq, if_pos ht0, if_neg (by simp [ht0]), if_neg (by simp [hJ]), add_zero, add_zero, ht0]
        have h1 : ((Pairs.filter fun AA' => tagOf AA' = (fun _ => 0)).card : ℝ) ≤ (n : ℝ) ^ m := by
          exact_mod_cast hfiber_diag
        calc ((Pairs.filter fun AA' => tagOf AA' = (fun _ => 0)).card : ℝ) * θ ^ m
            ≤ (n : ℝ) ^ m * θ ^ m := mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = μ := by rw [← mul_pow]
      · rw [hexp_eq, if_neg ht0, if_pos ⟨hJ, ht0⟩, if_neg (by simp [hJ]), zero_add, add_zero]
        have h1 : ((Pairs.filter fun AA' => tagOf AA' = t).card : ℝ) ≤ 4 * (n : ℝ) ^ (m - 1) := by
          exact_mod_cast hfiber_full t hJ ht0
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    · have ht0 : t ≠ (fun _ => 0) := by intro h; apply hJ; ext i; simp [Jof, h]
      rw [if_neg ht0, if_neg (fun h => hJ h.1), if_pos hJ, zero_add, zero_add]
      have h1 : ((Pairs.filter fun AA' => tagOf AA' = t).card : ℝ) ≤
          (n : ℝ) ^ (2 * m - (Jof t).card - 1) := by exact_mod_cast hfiber_partial t hJ
      refine le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) ?_
      have hJ_lt : (Jof t).card < m := by
        have hss : Jof t ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hJ⟩
        simpa using Finset.card_lt_card hss
      have hexp1 : 2 * m - (Jof t).card = (2 * m - (Jof t).card - 1) + 1 := by omega
      have hexp2 : (2 * m - (Jof t).card) + (Jof t).card = 2 * m := by omega
      rw [div_pow, one_pow, mul_div_assoc', div_mul_eq_mul_div, div_div,
        le_div_iff₀ (mul_pos hn_pos (pow_pos hqblk_pos _))]
      have hLHS :
          (n : ℝ) ^ (2 * m - (Jof t).card - 1) * θ ^ (2 * m - (Jof t).card) *
            ((n : ℝ) * qblk ^ (Jof t).card) = μ ^ 2 := by
        calc (n : ℝ) ^ (2 * m - (Jof t).card - 1) * θ ^ (2 * m - (Jof t).card) *
                ((n : ℝ) * qblk ^ (Jof t).card)
            = ((n : ℝ) ^ (2 * m - (Jof t).card - 1) * (n : ℝ)) *
                θ ^ (2 * m - (Jof t).card) * ((n : ℝ) ^ (Jof t).card * θ ^ (Jof t).card) := by
              rw [mul_pow]; ring
          _ = (n : ℝ) ^ (2 * m - (Jof t).card) * (n : ℝ) ^ (Jof t).card *
                (θ ^ (2 * m - (Jof t).card) * θ ^ (Jof t).card) := by
              rw [← pow_succ, ← hexp1]; ring
          _ = (n : ℝ) ^ (2 * m) * θ ^ (2 * m) := by rw [← pow_add, ← pow_add, hexp2]
          _ = ((n : ℝ) * θ) ^ (2 * m) := by rw [← mul_pow]
          _ = μ ^ 2 := by rw [show 2 * m = m * 2 by ring, pow_mul]
      rw [hLHS, mul_one]
  refine le_trans hsplit ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hpart1 : (∑ t : Fin m → Fin 3, if t = (fun _ => 0) then μ else 0) = μ := by simp
  have hpart2 :
      (∑ t : Fin m → Fin 3,
        if Jof t = Finset.univ ∧ t ≠ (fun _ => 0) then (4 : ℝ) * (n : ℝ) ^ (m - 1) * θ ^ m else 0) ≤
      (4 * (2 : ℝ) ^ m * μ) / (n : ℝ) := by
    have hle :
        (∑ t : Fin m → Fin 3,
          if Jof t = Finset.univ ∧ t ≠ (fun _ => 0) then (4 : ℝ) * (n : ℝ) ^ (m - 1) * θ ^ m else 0) ≤
        ∑ t : Fin m → Fin 3,
          if Jof t = Finset.univ then (4 : ℝ) * (n : ℝ) ^ (m - 1) * θ ^ m else 0 := by
      refine Finset.sum_le_sum fun t _ => ?_
      by_cases h1 : Jof t = Finset.univ
      · by_cases h2 : t = (fun _ => 0)
        · simp [h2]; positivity
        · simp [h2]
      · simp [h1]
    refine le_trans hle ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard_full : (Finset.univ.filter fun t : Fin m → Fin 3 => Jof t = Finset.univ).card ≤ 2 ^ m := by
      let e2 : (Fin m → Fin 2) ↪ (Fin m → Fin 3) :=
        ⟨fun f i => ⟨(f i).val, by omega⟩, fun f g h => funext fun i => Fin.ext (by
          have := congrArg Fin.val (congrFun h i); simpa using this)⟩
      have hsub : (Finset.univ.filter fun t : Fin m → Fin 3 => Jof t = Finset.univ) ⊆
          Finset.univ.map e2 := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        rw [Finset.mem_map]
        have hlt2 : ∀ i : Fin m, (t i).val < 2 := by
          intro i
          have hi : i ∈ Jof t := by rw [ht]; exact Finset.mem_univ i
          simp only [Jof, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have := (t i).isLt
          have hne : (t i).val ≠ 2 := fun hv => hi (Fin.ext hv)
          omega
        refine ⟨fun i => ⟨(t i).val, hlt2 i⟩, Finset.mem_univ _, funext fun i => Fin.ext rfl⟩
      calc (Finset.univ.filter fun t : Fin m → Fin 3 => Jof t = Finset.univ).card
          ≤ (Finset.univ.map e2).card := Finset.card_le_card hsub
        _ = 2 ^ m := by simp
    have hcardR : ((Finset.univ.filter fun t : Fin m → Fin 3 => Jof t = Finset.univ).card : ℝ) ≤ (2 : ℝ) ^ m := by
      exact_mod_cast hcard_full
    have hnm : (n : ℝ) ^ (m - 1) * θ ^ m = μ / (n : ℝ) := by
      rw [eq_div_iff hn_ne]
      calc (n : ℝ) ^ (m - 1) * θ ^ m * (n : ℝ)
          = ((n : ℝ) ^ (m - 1) * (n : ℝ)) * θ ^ m := by ring
        _ = (n : ℝ) ^ m * θ ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm]
        _ = μ := by rw [← mul_pow]
    calc ((Finset.univ.filter fun t : Fin m → Fin 3 => Jof t = Finset.univ).card : ℝ) *
            (4 * (n : ℝ) ^ (m - 1) * θ ^ m)
        ≤ (2 : ℝ) ^ m * (4 * (n : ℝ) ^ (m - 1) * θ ^ m) :=
          mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = 4 * (2 : ℝ) ^ m * ((n : ℝ) ^ (m - 1) * θ ^ m) := by ring
      _ = (4 * (2 : ℝ) ^ m * μ) / (n : ℝ) := by rw [hnm]; ring
  have hpart3 :
      (∑ t : Fin m → Fin 3,
        if Jof t ≠ Finset.univ then (μ ^ 2 / (n : ℝ)) * (1 / qblk) ^ (Jof t).card else 0) ≤
      (μ ^ 2 / (n : ℝ)) * (1 + 2 / qblk) ^ m := by
    have hle :
        (∑ t : Fin m → Fin 3,
          if Jof t ≠ Finset.univ then (μ ^ 2 / (n : ℝ)) * (1 / qblk) ^ (Jof t).card else 0) ≤
        ∑ t : Fin m → Fin 3, (μ ^ 2 / (n : ℝ)) * (1 / qblk) ^ (Jof t).card := by
      refine Finset.sum_le_sum fun t _ => ?_
      split_ifs
      · exact le_rfl
      · positivity
    refine le_trans hle ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hprod_id : ∀ t : Fin m → Fin 3,
        (1 / qblk) ^ (Jof t).card = ∏ i : Fin m, (if t i = 2 then (1 : ℝ) else 1 / qblk) := by
      intro t; rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    simp_rw [hprod_id]
    rw [← Fintype.prod_sum (f := fun (_ : Fin m) (x : Fin 3) => if x = 2 then (1 : ℝ) else 1 / qblk)]
    have hfin3 : (∑ x : Fin 3, if x = 2 then (1 : ℝ) else 1 / qblk) = 1 + 2 / qblk := by
      simp only [Fin.sum_univ_three, Fin.isValue, show (0 : Fin 3) ≠ 2 by decide,
        show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte]
      ring
    simp_rw [hfin3]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  linarith

private lemma avg_collision_potential_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {Seed₁ : Type*} [Fintype Seed₁] [Nonempty Seed₁]
    (Ω : Finset G) (m : ℕ) (θ : ℝ) (mem : Seed₁ → G → Bool)
    (hm : 2 ≤ m)
    (hn : 4096 * m ≤ Ω.card)
    (hgord : Fintype.card G ≤ Ω.card + 1)
    (hθ_pos : 0 < θ)
    (hqblk_ge : (4096 * m : ℝ) ≤ (Ω.card : ℝ) * θ)
    (hμ_ge : 16 * (Fintype.card G : ℝ) ≤ ((Ω.card : ℝ) * θ) ^ m)
    (h2tors : (Finset.univ.filter fun g : G => g + g = 0).card ≤ 4)
    (hΩ : ∀ s g, mem s g = true → g ∈ Ω)
    (h1pt : ∀ A ∈ Ω,
      ((Finset.univ.filter fun s : Seed₁ => mem s A = true).card : ℝ) /
        (Fintype.card Seed₁ : ℝ) = θ)
    (h2pt : ∀ A ∈ Ω, ∀ B ∈ Ω, B ≠ A → B ≠ -A →
      ((Finset.univ.filter fun s : Seed₁ => mem s A = true ∧ mem s B = true).card : ℝ) /
        (Fintype.card Seed₁ : ℝ) ≤ θ ^ 2) :
    (∑ S : Fin m → Seed₁,
        collisionPotentialAdd (((Ω.card : ℝ) * θ) ^ m)
          (fun i => Finset.univ.filter fun g => mem (S i) g = true)) /
      (Fintype.card (Fin m → Seed₁) : ℝ) ≤ (373 : ℝ) / 336 := by
  set n : ℕ := Ω.card
  set gord : ℕ := Fintype.card G
  set qblk : ℝ := (n : ℝ) * θ
  set μ : ℝ := qblk ^ m
  set F : (Fin m → Seed₁) → Fin m → Finset G :=
    fun S i => Finset.univ.filter fun g => mem (S i) g = true
  have hΩ_pos : 0 < n := by omega
  have hqblk_pos : 0 < qblk := by
    have : (0 : ℝ) < (4096 * m : ℝ) := by exact_mod_cast (by omega : 0 < 4096 * m)
    linarith
  have hμ_pos : 0 < μ := pow_pos hqblk_pos m
  have hVarW := avg_productSize_var_le Ω m θ mem hθ_pos hΩ_pos hΩ h1pt h2pt
  have hEC := avg_collisionEnergy_le Ω m θ mem (by omega) hΩ_pos hθ_pos h2tors hΩ h1pt h2pt
  dsimp only at hVarW hEC
  have havg_phi :
      (∑ S : Fin m → Seed₁, collisionPotentialAdd μ (F S)) /
        (Fintype.card (Fin m → Seed₁) : ℝ) =
      ((gord : ℝ) * ((∑ S : Fin m → Seed₁, (collisionEnergyAdd (F S) : ℝ)) /
          (Fintype.card (Fin m → Seed₁) : ℝ)) +
        64 * ((∑ S : Fin m → Seed₁, ((productSize (F S) : ℝ) - μ) ^ 2) /
          (Fintype.card (Fin m → Seed₁) : ℝ))) / μ ^ 2 := by
    unfold collisionPotentialAdd
    simp_rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [havg_phi]
  have hcomb :
      ((gord : ℝ) * ((∑ S : Fin m → Seed₁, (collisionEnergyAdd (F S) : ℝ)) /
          (Fintype.card (Fin m → Seed₁) : ℝ)) +
        64 * ((∑ S : Fin m → Seed₁, ((productSize (F S) : ℝ) - μ) ^ 2) /
          (Fintype.card (Fin m → Seed₁) : ℝ))) / μ ^ 2 ≤
      (gord : ℝ) / μ + ((gord : ℝ) / (n : ℝ)) * (4 * (2 : ℝ) ^ m / μ) +
        ((gord : ℝ) / (n : ℝ)) * (1 + 2 / qblk) ^ m +
        64 * ((1 + 2 / qblk) ^ m - 1) := by
    have hnum :
        (gord : ℝ) * ((∑ S : Fin m → Seed₁, (collisionEnergyAdd (F S) : ℝ)) /
          (Fintype.card (Fin m → Seed₁) : ℝ)) +
        64 * ((∑ S : Fin m → Seed₁, ((productSize (F S) : ℝ) - μ) ^ 2) /
          (Fintype.card (Fin m → Seed₁) : ℝ)) ≤
        (gord : ℝ) * (μ + (4 * (2 : ℝ) ^ m * μ) / (n : ℝ) + (μ ^ 2 / (n : ℝ)) * (1 + 2 / qblk) ^ m) +
        64 * (μ ^ 2 * ((1 + 2 / qblk) ^ m - 1)) := by
      have h1 := mul_le_mul_of_nonneg_left hEC (by positivity : (0 : ℝ) ≤ (gord : ℝ))
      have h2 := mul_le_mul_of_nonneg_left hVarW (by norm_num : (0 : ℝ) ≤ 64)
      linarith
    have hdiv := div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ μ ^ 2)
    refine le_trans hdiv ?_
    have hμ_ne : μ ≠ 0 := ne_of_gt hμ_pos
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp [hμ_ne, hn_ne]
    ring_nf
    exact le_rfl
  refine le_trans hcomb ?_
  have h1 : (gord : ℝ) / μ ≤ 1 / 16 := by
    rw [div_le_div_iff₀ hμ_pos (by norm_num)]; linarith
  have hn_ge : (8192 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 8192 ≤ n)
  have h2 : (gord : ℝ) / (n : ℝ) ≤ 8193 / 8192 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have hg : (gord : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hgord
    nlinarith
  have hmx : (m : ℝ) * (2 / qblk) ≤ 1 / 2048 := by
    rw [mul_div_assoc', div_le_div_iff₀ hqblk_pos (by norm_num)]; linarith
  have hpow : (1 + 2 / qblk) ^ m ≤ 2048 / 2047 := by
    have h := one_add_pow_le_inv_one_sub (x := 2 / qblk) (m := m) (by positivity) (by linarith)
    refine le_trans h ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h2m_div_μ : (2 : ℝ) ^ m / μ ≤ 1 / 16777216 := by
    have hq8192 : (8192 : ℝ) ≤ qblk := by
      have : (8192 : ℝ) ≤ (4096 * m : ℝ) := by exact_mod_cast (by omega : 8192 ≤ 4096 * m)
      linarith
    have hbase : 2 / qblk ≤ 1 / 4096 := by
      rw [div_le_div_iff₀ hqblk_pos (by norm_num)]; linarith
    calc (2 : ℝ) ^ m / μ = (2 / qblk) ^ m := by rw [div_pow]
      _ ≤ (1 / 4096 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) hbase m
      _ ≤ (1 / 4096 : ℝ) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 1 / 16777216 := by norm_num
  have hpow_nn : 0 ≤ (1 + 2 / qblk) ^ m := by positivity
  have h2m_nn : 0 ≤ 4 * (2 : ℝ) ^ m / μ := by positivity
  have hterm2 : ((gord : ℝ) / (n : ℝ)) * (4 * (2 : ℝ) ^ m / μ) ≤
      (8193 / 8192 : ℝ) * (4 / 16777216) := by
    have h4 : 4 * (2 : ℝ) ^ m / μ ≤ 4 / 16777216 := by rw [mul_div_assoc]; linarith
    exact mul_le_mul h2 h4 h2m_nn (by norm_num)
  have hterm3 : ((gord : ℝ) / (n : ℝ)) * (1 + 2 / qblk) ^ m ≤
      (8193 / 8192 : ℝ) * (2048 / 2047) :=
    mul_le_mul h2 hpow hpow_nn (by norm_num)
  linarith

/-! ### Part 5: Elliptic-curve and multiplicative cases, and `solution` -/

private lemma ec_collision_potential_le :
    ∀ (p m : ℕ) [Fact p.Prime], 3 < p → 2 ≤ m →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let gord := Fintype.card E.toAffine.Point
        let n := gord - 1
        64 ≤ gord → 4096 * m ≤ n →
        let T := hashThreshold p n m gord
        let μ := (qBlk p n T) ^ m
        (∑ S : ECSeed p m, collisionPotentialAdd μ (ecFactorBlock E T S)) /
          (Fintype.card (ECSeed p m) : ℝ) ≤ (373 : ℝ) / 336 := by
    intro p m _ hp3 hm E _
    let _ := ecPointFintype E
    dsimp only
    intro hgord64 hn4096
    have hp : p.Prime := Fact.out
    have : NeZero p := ⟨hp.ne_zero⟩
    let gord := Fintype.card E.toAffine.Point
    let n := gord - 1
    let T := hashThreshold p n m gord
    let θ := (T : ℝ) / (p : ℝ)
    let Ω : Finset E.toAffine.Point := Finset.univ.erase 0
    have hΩcard : Ω.card = n := by simp [Ω, n, gord]
    have hparams := hashThreshold_params (p := p) (n := n) (m := m) (gord := gord)
      (by omega) hm hn4096 (by omega)
    obtain ⟨_, hTp, hθ_pos, _, hqblk_eq, hqblk_ge, hμ_ge⟩ := hparams
    let Seed₁ := Bool → Fin (p - 1) × Fin p
    have : Nonempty Seed₁ := ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    let mem : Seed₁ → E.toAffine.Point → Bool := fun s P =>
      match P with
      | .zero => false
      | .some x y _ =>
        let ε : Bool := decide (y.val % 2 = 1)
        let ab := s ε
        decide (((ab.1.val + 1) * x.val + ab.2.val) % p < T)
    have hmem_eq : ∀ (S : ECSeed p m) (i : Fin m),
        ecFactorBlock E T S i = Finset.univ.filter fun g => mem (S i) g = true := by
      intro S i
      unfold ecFactorBlock
      congr 1
    have hS1_card : (Fintype.card Seed₁ : ℝ) = ((p - 1 : ℕ) : ℝ) * (p : ℝ) * (((p - 1 : ℕ) : ℝ) * (p : ℝ)) := by
      have : Fintype.card Seed₁ = ((p - 1) * p) ^ 2 := by
        simp [Seed₁, Fintype.card_pi, Fintype.card_prod]
      rw [this]; push_cast; ring
    let eBool : Seed₁ ≃ (Fin (p - 1) × Fin p) × (Fin (p - 1) × Fin p) :=
      { toFun := fun s => (s false, s true)
        invFun := fun ab b => if b then ab.2 else ab.1
        left_inv := fun s => funext fun b => by cases b <;> rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    have h1pt : ∀ A ∈ Ω,
        ((Finset.univ.filter fun s : Seed₁ => mem s A = true).card : ℝ) /
          (Fintype.card Seed₁ : ℝ) = θ := by
      intro A hA
      cases A with
      | zero =>
        change (0 : E.toAffine.Point) ∈ Ω at hA
        simp [Ω] at hA
      | some x y h =>
        let ε : Bool := decide (y.val % 2 = 1)
        let cond : Fin (p - 1) × Fin p → Prop := fun ab =>
          ((ab.1.val + 1) * x.val + ab.2.val) % p < T
        have hcard : (Finset.univ.filter fun s : Seed₁ => mem s (.some x y h) = true).card =
            ((p - 1) * p) * ((p - 1) * T) := by
          have h1 : (Finset.univ.filter fun s : Seed₁ => mem s (.some x y h) = true).card =
              (Finset.univ.filter fun ab : (Fin (p - 1) × Fin p) × (Fin (p - 1) × Fin p) =>
                cond (if ε then ab.2 else ab.1)).card := by
            rw [Finset.card_filter, Finset.card_filter]
            refine Fintype.sum_equiv eBool _ _ fun s => ?_
            cases hε : ε
            · simp [mem, cond, eBool, ε, hε, decide_eq_true_eq]
            · simp [mem, cond, eBool, ε, hε, decide_eq_true_eq]
          rw [h1]
          cases hε : ε
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hprod : (Finset.univ.filter fun ab : (Fin (p - 1) × Fin p) × (Fin (p - 1) × Fin p) =>
                cond ab.1) = (Finset.univ.filter cond) ×ˢ Finset.univ := by
              ext ⟨a, b⟩; simp
            rw [hprod, Finset.card_product, affine_hash_1pt_card hTp x]
            simp [T, mul_comm]
          · simp only [↓reduceIte]
            have hprod : (Finset.univ.filter fun ab : (Fin (p - 1) × Fin p) × (Fin (p - 1) × Fin p) =>
                cond ab.2) = Finset.univ ×ˢ (Finset.univ.filter cond) := by
              ext ⟨a, b⟩; simp
            rw [hprod, Finset.card_product, affine_hash_1pt_card hTp x]
            simp [T]
        rw [hcard, hS1_card]
        push_cast
        have hpm1_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : p - 1 ≠ 0)
        have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
        dsimp [θ]
        field_simp [hpm1_ne, hp_ne]
    have h2pt : ∀ A ∈ Ω, ∀ B ∈ Ω, B ≠ A → B ≠ -A →
        ((Finset.univ.filter fun s : Seed₁ => mem s A = true ∧ mem s B = true).card : ℝ) /
          (Fintype.card Seed₁ : ℝ) ≤ θ ^ 2 := by
      intro A hA B hB hBA hBneg
      cases A with
      | zero =>
        change (0 : E.toAffine.Point) ∈ Ω at hA
        simp [Ω] at hA
      | some x₁ y₁ h₁ =>
        cases B with
        | zero =>
          change (0 : E.toAffine.Point) ∈ Ω at hB
          simp [Ω] at hB
        | some x₂ y₂ h₂ =>
          have hxne : x₁ ≠ x₂ := by
            intro hxeq
            rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := h₁) (h₂ := h₂)).mp hxeq with h | h
            · exact hBA h.symm
            · exact hBneg (by rw [h, neg_neg])
          let ε₁ : Bool := decide (y₁.val % 2 = 1)
          let ε₂ : Bool := decide (y₂.val % 2 = 1)
          let cond₁ : Fin (p - 1) × Fin p → Prop := fun ab =>
            ((ab.1.val + 1) * x₁.val + ab.2.val) % p < T
          let cond₂ : Fin (p - 1) × Fin p → Prop := fun ab =>
            ((ab.1.val + 1) * x₂.val + ab.2.val) % p < T
          have h1 : (Finset.univ.filter fun s : Seed₁ =>
                mem s (.some x₁ y₁ h₁) = true ∧ mem s (.some x₂ y₂ h₂) = true).card =
              (Finset.univ.filter fun ab : (Fin (p - 1) × Fin p) × (Fin (p - 1) × Fin p) =>
                cond₁ (if ε₁ then ab.2 else ab.1) ∧ cond₂ (if ε₂ then ab.2 else ab.1)).card := by
            rw [Finset.card_filter, Finset.card_filter]
            refine Fintype.sum_equiv eBool _ _ fun s => ?_
            cases hε1 : ε₁ <;> cases hε2 : ε₂ <;>
              simp [mem, cond₁, cond₂, eBool, ε₁, ε₂, hε1, hε2, decide_eq_true_eq]
          rw [h1]
          cases hε1 : ε₁ <;> cases hε2 : ε₂
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hprod : (Finset.univ.filter fun ab : (Fin (p - 1) × Fin p) × (Fin (p - 1) × Fin p) =>
                cond₁ ab.1 ∧ cond₂ ab.1) =
                (Finset.univ.filter fun a => cond₁ a ∧ cond₂ a) ×ˢ Finset.univ := by
              ext ⟨a, b⟩; simp
            rw [hprod, Finset.card_product, affine_hash_2pt_card hTp hxne, hS1_card]
            have hcard_u : (Finset.univ : Finset (Fin (p - 1) × Fin p)).card = (p - 1) * p := by simp
            rw [hcard_u]
            push_cast
            have hle := pair_prob_le_sq (p := p) (T := T) (by omega) hTp
            push_cast at hle
            have hpm1_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : p - 1 ≠ 0)
            have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
            have heq : ((T * (T - 1) : ℕ) : ℝ) * (((p - 1 : ℕ) : ℝ) * (p : ℝ)) /
                (((p - 1 : ℕ) : ℝ) * (p : ℝ) * (((p - 1 : ℕ) : ℝ) * (p : ℝ))) =
                ((T * (T - 1) : ℕ) : ℝ) / (((p - 1 : ℕ) : ℝ) * (p : ℝ)) := by
              field_simp [hpm1_ne, hp_ne]
            push_cast at heq
            rw [heq]; exact hle
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hprod : (Finset.univ.filter fun ab : (Fin (p - 1) × Fin p) × (Fin (p - 1) × Fin p) =>
                cond₁ ab.1 ∧ cond₂ ab.2) =
                (Finset.univ.filter cond₁) ×ˢ (Finset.univ.filter cond₂) := by
              ext ⟨a, b⟩; simp
            rw [hprod, Finset.card_product, affine_hash_1pt_card hTp x₁,
              affine_hash_1pt_card hTp x₂, hS1_card]
            push_cast
            have hpm1_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : p - 1 ≠ 0)
            have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
            dsimp [θ]; field_simp [hpm1_ne, hp_ne]; exact le_rfl
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hprod : (Finset.univ.filter fun ab : (Fin (p - 1) × Fin p) × (Fin (p - 1) × Fin p) =>
                cond₁ ab.2 ∧ cond₂ ab.1) =
                (Finset.univ.filter cond₂) ×ˢ (Finset.univ.filter cond₁) := by
              ext ⟨a, b⟩; simp [and_comm]
            rw [hprod, Finset.card_product, affine_hash_1pt_card hTp x₁,
              affine_hash_1pt_card hTp x₂, hS1_card]
            push_cast
            have hpm1_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : p - 1 ≠ 0)
            have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
            dsimp [θ]; field_simp [hpm1_ne, hp_ne]; exact le_rfl
          · simp only [↓reduceIte]
            have hprod : (Finset.univ.filter fun ab : (Fin (p - 1) × Fin p) × (Fin (p - 1) × Fin p) =>
                cond₁ ab.2 ∧ cond₂ ab.2) =
                Finset.univ ×ˢ (Finset.univ.filter fun a => cond₁ a ∧ cond₂ a) := by
              ext ⟨a, b⟩; simp
            rw [hprod, Finset.card_product, affine_hash_2pt_card hTp hxne, hS1_card]
            have hcard_u : (Finset.univ : Finset (Fin (p - 1) × Fin p)).card = (p - 1) * p := by simp
            rw [hcard_u]
            push_cast
            have hle := pair_prob_le_sq (p := p) (T := T) (by omega) hTp
            push_cast at hle
            have hpm1_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : p - 1 ≠ 0)
            have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
            have heq : (((p - 1 : ℕ) : ℝ) * (p : ℝ)) * ((T * (T - 1) : ℕ) : ℝ) /
                (((p - 1 : ℕ) : ℝ) * (p : ℝ) * (((p - 1 : ℕ) : ℝ) * (p : ℝ))) =
                ((T * (T - 1) : ℕ) : ℝ) / (((p - 1 : ℕ) : ℝ) * (p : ℝ)) := by
              field_simp [hpm1_ne, hp_ne]
            push_cast at heq
            rw [heq]; exact hle
    have hmain := avg_collision_potential_le (G := E.toAffine.Point) (Seed₁ := Seed₁)
      Ω m θ mem hm (by rw [hΩcard]; exact hn4096) (by rw [hΩcard]; omega) hθ_pos
      (by rw [hΩcard, ← hqblk_eq]; exact hqblk_ge)
      (by rw [hΩcard, ← hqblk_eq]; exact hμ_ge)
      (ec_two_torsion_card_le hp3 E)
      (fun s P hP => by
        cases P with
        | zero => simp [mem] at hP
        | some x y h => simp [Ω])
      h1pt h2pt
    have hμ_eq : ((Ω.card : ℝ) * θ) ^ m = (qBlk p n T) ^ m := by
      rw [hΩcard, hqblk_eq]
    rw [hμ_eq] at hmain
    convert hmain using 2
    refine Finset.sum_congr rfl fun S _ => ?_
    congr 1

private lemma fp_collision_potential_le :
    ∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
      let gord := p - 1
      let n := p - 1
      64 ≤ gord → 4096 * m ≤ n →
      let T := hashThreshold p n m gord
      let μ := (qBlk p n T) ^ m
      (∑ S : FpSeed p m, collisionPotentialMul μ (fpFactorBlock (p := p) T S)) /
        (Fintype.card (FpSeed p m) : ℝ) ≤ (373 : ℝ) / 336 := by
    intro p m _ hm
    dsimp only
    intro hgord64 hn4096
    have hp : p.Prime := Fact.out
    have : NeZero p := ⟨hp.ne_zero⟩
    let gord := p - 1
    let n := p - 1
    let T := hashThreshold p n m gord
    let θ := (T : ℝ) / (p : ℝ)
    let Ω : Finset (Additive (ZMod p)ˣ) := Finset.univ
    have hcard_units : Fintype.card (Additive (ZMod p)ˣ) = p - 1 := by
      rw [Fintype.card_congr Additive.toMul, ZMod.card_units]
    have hΩcard : Ω.card = n := by simp [Ω, n, hcard_units]
    have hparams := hashThreshold_params (p := p) (n := n) (m := m) (gord := gord)
      hp.two_le hm hn4096 (by omega)
    obtain ⟨_, hTp, hθ_pos, _, hqblk_eq, hqblk_ge, hμ_ge⟩ := hparams
    let Seed₁ := Fin (p - 1) × Fin p
    have : Nonempty Seed₁ := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    let mem : Seed₁ → Additive (ZMod p)ˣ → Bool := fun ab a =>
      decide (((ab.1.val + 1) * ((Additive.toMul a : (ZMod p)ˣ) : ZMod p).val + ab.2.val) % p < T)
    have h1pt : ∀ A ∈ Ω,
        ((Finset.univ.filter fun s : Seed₁ => mem s A = true).card : ℝ) /
          (Fintype.card Seed₁ : ℝ) = θ := by
      intro A _
      let x : ZMod p := (Additive.toMul A : (ZMod p)ˣ)
      have hcard : (Finset.univ.filter fun s : Seed₁ => mem s A = true).card = (p - 1) * T := by
        simpa [mem, x] using affine_hash_1pt_card hTp x
      rw [hcard]
      have hSc : Fintype.card Seed₁ = (p - 1) * p := by simp [Seed₁]
      rw [hSc]; push_cast
      have hpm1_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : p - 1 ≠ 0)
      have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
      dsimp [θ]; field_simp [hpm1_ne, hp_ne]
    have h2pt : ∀ A ∈ Ω, ∀ B ∈ Ω, B ≠ A → B ≠ -A →
        ((Finset.univ.filter fun s : Seed₁ => mem s A = true ∧ mem s B = true).card : ℝ) /
          (Fintype.card Seed₁ : ℝ) ≤ θ ^ 2 := by
      intro A _ B _ hBA _
      let x₁ : ZMod p := (Additive.toMul A : (ZMod p)ˣ)
      let x₂ : ZMod p := (Additive.toMul B : (ZMod p)ˣ)
      have hxne : x₁ ≠ x₂ := fun h => hBA (Additive.toMul.injective (Units.ext h.symm))
      have hcard : (Finset.univ.filter fun s : Seed₁ => mem s A = true ∧ mem s B = true).card =
          T * (T - 1) := by
        simpa [mem, x₁, x₂] using affine_hash_2pt_card hTp hxne
      rw [hcard]
      have hSc : Fintype.card Seed₁ = (p - 1) * p := by simp [Seed₁]
      rw [hSc]
      exact pair_prob_le_sq hp.two_le hTp
    have hmain := avg_collision_potential_le (G := Additive (ZMod p)ˣ) (Seed₁ := Seed₁)
      Ω m θ mem hm (by rw [hΩcard]; exact hn4096) (by rw [hΩcard, hcard_units]; omega) hθ_pos
      (by rw [hΩcard, ← hqblk_eq]; exact hqblk_ge)
      (by rw [hΩcard, ← hqblk_eq, hcard_units]; exact hμ_ge)
      fp_two_torsion_card_le
      (fun _ _ _ => Finset.mem_univ _)
      h1pt h2pt
    have hμ_eq : ((Ω.card : ℝ) * θ) ^ m = (qBlk p n T) ^ m := by
      rw [hΩcard, hqblk_eq]
    rw [hμ_eq] at hmain
    have hpot_eq : ∀ S : FpSeed p m,
        collisionPotentialMul ((qBlk p n T) ^ m) (fpFactorBlock (p := p) T S) =
        collisionPotentialAdd ((qBlk p n T) ^ m)
          (fun i => Finset.univ.filter fun g : Additive (ZMod p)ˣ => mem (S i) g = true) := by
      intro S
      have hcard_eq : Fintype.card (ZMod p)ˣ = Fintype.card (Additive (ZMod p)ˣ) :=
        (Fintype.card_congr Additive.toMul).symm
      have hC_eq : collisionEnergyMul (fpFactorBlock (p := p) T S) =
          collisionEnergyAdd (fun i => Finset.univ.filter fun g : Additive (ZMod p)ˣ => mem (S i) g = true) := by
        unfold collisionEnergyMul collisionEnergyAdd repCountMul repCountAdd
        refine Fintype.sum_equiv Additive.ofMul _ _ fun g => ?_
        refine congrArg (· ^ 2) ?_
        refine Finset.card_bij (fun A _ i => Additive.ofMul (A i)) ?_ ?_ ?_
        · intro A hA
          simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ, true_and] at hA ⊢
          refine ⟨fun i => ?_, by simpa [ofMul_prod] using congrArg Additive.ofMul hA.2⟩
          have hi := hA.1 i
          rw [fpFactorBlock, Finset.mem_filter] at hi
          exact hi.2
        · intro A₁ _ A₂ _ h
          funext i
          exact Additive.ofMul.injective (congrFun h i)
        · intro A hA
          simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ, true_and] at hA ⊢
          refine ⟨fun i => Additive.toMul (A i), ⟨fun i => ?_, ?_⟩, funext fun i => rfl⟩
          · have hi := hA.1 i
            rw [fpFactorBlock, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hi⟩
          · have := congrArg Additive.toMul hA.2
            simpa [toMul_sum] using this
      have hW_eq : productSize (fpFactorBlock (p := p) T S) =
          productSize (fun i => Finset.univ.filter fun g : Additive (ZMod p)ˣ => mem (S i) g = true) := by
        unfold productSize
        refine Finset.prod_congr rfl fun i _ => ?_
        refine Finset.card_bij (fun a _ => Additive.ofMul a) ?_ ?_ ?_
        · intro a ha
          rw [fpFactorBlock, Finset.mem_filter] at ha
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ha.2⟩
        · intro a₁ _ a₂ _ h; exact Additive.ofMul.injective h
        · intro a ha
          rw [Finset.mem_filter] at ha
          refine ⟨Additive.toMul a, ?_, rfl⟩
          rw [fpFactorBlock, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ha.2⟩
      unfold collisionPotentialMul collisionPotentialAdd
      rw [hcard_eq, hC_eq, hW_eq]
    have hsum_eq :
        (∑ S : FpSeed p m, collisionPotentialMul ((qBlk p n T) ^ m) (fpFactorBlock (p := p) T S)) =
        (∑ S : FpSeed p m, collisionPotentialAdd ((qBlk p n T) ^ m)
          (fun i => Finset.univ.filter fun g : Additive (ZMod p)ˣ => mem (S i) g = true)) :=
      Finset.sum_congr rfl fun S _ => hpot_eq S
    rw [hsum_eq]
    exact hmain

theorem solution :
    (∀ (p m : ℕ) [Fact p.Prime], 3 < p → 2 ≤ m →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let gord := Fintype.card E.toAffine.Point
        let n := gord - 1
        64 ≤ gord → 4096 * m ≤ n →
        let T := hashThreshold p n m gord
        let μ := (qBlk p n T) ^ m
        (∑ S : ECSeed p m, collisionPotentialAdd μ (ecFactorBlock E T S)) /
          (Fintype.card (ECSeed p m) : ℝ) ≤ (373 : ℝ) / 336) ∧
    (∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
      let gord := p - 1
      let n := p - 1
      64 ≤ gord → 4096 * m ≤ n →
      let T := hashThreshold p n m gord
      let μ := (qBlk p n T) ^ m
      (∑ S : FpSeed p m, collisionPotentialMul μ (fpFactorBlock (p := p) T S)) /
        (Fintype.card (FpSeed p m) : ℝ) ≤ (373 : ℝ) / 336) :=
  ⟨ec_collision_potential_le, fp_collision_potential_le⟩
